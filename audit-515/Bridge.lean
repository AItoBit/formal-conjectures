noncomputable def toFC (C : Erdos515.LocallyRectifiablePath) : FC515.PolygonalRay where
  vertex := C.vertex
  tendsToInfinity := C.tendsToInfinity

@[category API, AMS 30]
theorem lineIntegral_toFC (C : Erdos515.LocallyRectifiablePath)
    (f : ℂ → ℂ) (lambda : ℝ) :
    FC515.lineIntegral (toFC C) f lambda = Erdos515.lineIntegral C f lambda := by
  rfl

@[category API, AMS 30]
theorem external_implies_fc : True ↔ ∀ f : ℂ → ℂ, Differentiable ℂ f →
    (¬ ∃ p : ℂ[X], ∀ z : ℂ, p.eval z = f z) →
    ∃ C : FC515.PolygonalRay, ∀ lambda : ℝ, 0 < lambda →
      FC515.lineIntegral C f lambda ≠ ⊤ := by
  constructor
  · intro _ f hf htrans
    obtain ⟨C, hC⟩ := Erdos515.erdos_515 hf htrans
    exact ⟨toFC C, fun lambda hl => by
      simpa only [lineIntegral_toFC] using hC lambda hl⟩
  · intro _
    trivial
