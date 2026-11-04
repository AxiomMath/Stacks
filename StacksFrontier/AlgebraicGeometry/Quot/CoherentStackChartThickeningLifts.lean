module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackAxiomHelpers.CoherentTangentBridge
public import StacksFrontier.Deformation.Artin.Obstruction.DualSituation
public import StacksFrontier.Deformation.Artin.Versality.DiagonalFibreDescent
public import StacksFrontier.AlgebraicGeometry.Smooth.FormallySmoothScheme

/-!
# Lifts of an object of `Coh_{X/Y}` over a chart across a square-zero thickening

Let `x` be an object of `Coh_{X/Y}` over `Spec A`, with `Y` final, and let `A' → A` be a
square-zero thickening of `Spec A` over `S` (`Deformation.Artin.SquareZeroThickening`). A lift of
`x` across it in the sense of the deformation theory of categories fibred in groupoids (an object
of the fibre of `Under.post p` over `Spec A ⟶ Spec A'`) is a lift of the module of `x` to `X_{A'}`
in the sense of `AlgebraicGeometry.Space.CoherentSituation.ThickeningLift`, and one of the two
kinds of lifts exists exactly when the other does. On global sections, the kernel of
`Γ(Spec A') ⟶ Γ(Spec A)` is identified with the kernel of `A' → A`, naturally in the thickening.

## Main definitions

* `AlgebraicGeometry.Space.CoherentSituation.thickeningTestScheme`,
  `AlgebraicGeometry.Space.CoherentSituation.thickeningTestMap`: `Spec A ⟶ Spec A'` as a morphism
  of test schemes over a final `Y`.
* `AlgebraicGeometry.Space.CoherentSituation.thickeningLiftOfFiber`: the lift of the module of `x`
  attached to a lift of `x` to `A'`.
* `AlgebraicGeometry.Space.CoherentSituation.kernelModuleIso`: the kernel of
  `Γ(Spec A') ⟶ Γ(Spec A)` is the kernel of `A' → A`.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.isFirstOrderThickening_thickeningTestMap`:
  `Spec A ⟶ Spec A'` is a first order thickening of test schemes.
* `AlgebraicGeometry.Space.CoherentSituation.nonempty_fiber_iff_nonempty_thickeningLift`: a lift
  of `x` across `A' → A` exists exactly when its module lifts to `X_{A'}`.
* `AlgebraicGeometry.Space.CoherentSituation.kernelModuleIso_hom_apply`: the kernel
  identification is natural in the thickening.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.CoherentSituation

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (D : CoherentSituation B S hS)
  (hY : IsTerminal D.Y)
  {A : Type u} [CommRing A] {toS : Spec (.of A) ⟶ S} {hA : B.Contains (Spec (.of A))}

/-- The test scheme `Spec A'` of a square-zero thickening, over a final `Y`. -/
def thickeningTestScheme {A' : Type u} [CommRing A']
    (T : Deformation.Artin.SquareZeroThickening A B S hS toS hA A') : SchemesOver D.Y :=
  CostructuredArrow.mk (hY.from ((schemeSpaceFunctor B S hS).obj
    (Over.mk T.toS' : BigFppfOver B S hS)))

variable (x : CoherentObject D)
  (hx : (coherentCFG D).val.p.obj x = Deformation.Artin.algebraOver A B S hS toS hA)

/-- The closed immersion `Spec A ⟶ Spec A'` under `x`, as a morphism of test schemes. -/
def thickeningTestMap {A' : Type u} [CommRing A']
    (T : Deformation.Artin.SquareZeroThickening A B S hS toS hA A') :
    x.T ⟶ D.thickeningTestScheme hY T :=
  CostructuredArrow.homMk (eqToHom hx ≫ T.arrow) (hY.hom_ext _ _)

/-- **`Spec A ⟶ Spec A'` is a first order thickening of test schemes.** -/
theorem isFirstOrderThickening_thickeningTestMap {A' : Type u} [CommRing A']
    (T : Deformation.Artin.SquareZeroThickening A B S hS toS hA A') :
    Stacks.Thickenings.IsFirstOrderThickening
      ((BigFppfOver.toScheme B S hS).map (D.thickeningTestMap hY x hx T).left) := by
  change Stacks.Thickenings.IsFirstOrderThickening
    ((BigFppfOver.toScheme B S hS).map (eqToHom hx ≫ T.arrow))
  rw [CategoryTheory.Functor.map_comp]
  refine Deformation.Artin.isFirstOrderThickening_iso_comp _ _ ?_
  change Stacks.Thickenings.IsFirstOrderThickening (B.inclusion.map T.arrow.left)
  rw [T.arrow_spec]
  exact Stacks.Smooth.isFirstOrderThickening_specMap (CommRingCat.ofHom T.q)
    T.squareZeroSurjection.1 T.squareZeroSurjection.2

variable {D x hx} {A' : Type u} [CommRing A']
  {T : Deformation.Artin.SquareZeroThickening A B S hS toS hA A'}
  (y : (Under.post (coherentCFG D).val.p).Fiber (Under.mk (eqToHom hx ≫ T.arrow)))

include hY in
/-- The test scheme of a lift of `x` to `A'` is `Spec A'`. -/
theorem thickeningLift_T_eq : y.1.right.T = D.thickeningTestScheme hY T :=
  D.schemesOver_ext_of_isTerminal hY (congrArg (fun t => t.right) y.2)

/-- The arrow `x ⟶ y` of a lift, as a morphism of `Coh_{X/Y}`. -/
def thickeningLiftArrow : CoherentHom x y.1.right := y.1.hom

/-- The arrow of a lift lies over `Spec A ⟶ Spec A'`. -/
theorem thickeningTestMap_comp_eqToHom :
    D.thickeningTestMap hY x hx T ≫ eqToHom (thickeningLift_T_eq hY y).symm =
      (thickeningLiftArrow y).base := by
  have hw := Under.w (eqToHom y.2)
  rw [Under.eqToHom_right] at hw
  have hw' : (coherentCFG D).val.p.map y.1.hom ≫ eqToHom (congrArg (fun t => t.right) y.2) =
      eqToHom hx ≫ T.arrow := hw
  apply CostructuredArrow.hom_ext
  rw [CostructuredArrow.comp_left, CostructuredArrow.eqToHom_left]
  change (eqToHom hx ≫ T.arrow) ≫ _ = (coherentCFG D).val.p.map y.1.hom
  exact (comp_eqToHom_iff _ _ _).2 hw'.symm

/-- The module comparison of the lift attached to a lift of `x` to `A'`. -/
def thickeningLiftFibreIso :
    (modulePullback B S hS (D.relativeMap (D.thickeningTestMap hY x hx T))).obj
        ((modulePullback B S hS (D.relativeMap (eqToHom (thickeningLift_T_eq hY y).symm))).obj
          y.1.right.F) ≅ x.F :=
  ((D.compComparison _ (eqToHom (thickeningLift_T_eq hY y).symm)).app y.1.right.F).symm ≪≫
    eqToIso (congrArg (fun k => (modulePullback B S hS (D.relativeMap k)).obj y.1.right.F)
      (thickeningTestMap_comp_eqToHom hY y)) ≪≫
    @asIso _ _ _ _ (thickeningLiftArrow y).fibre (thickeningLiftArrow y).isIso_fibre

/-- **The lift of the module of `x` attached to a lift of `x` to `A'`.** -/
def thickeningLiftOfFiber : D.ThickeningLift x (D.thickeningTestMap hY x hx T) where
  F := (modulePullback B S hS (D.relativeMap (eqToHom (thickeningLift_T_eq hY y).symm))).obj
    y.1.right.F
  quasicoherent := (pullbackObject' (modulePullbackStabilityOfFinitePresentation B S hS)
    y.1.right (eqToHom (thickeningLift_T_eq hY y).symm)).quasicoherent
  finitePresentation := (pullbackObject' (modulePullbackStabilityOfFinitePresentation B S hS)
    y.1.right (eqToHom (thickeningLift_T_eq hY y).symm)).finitePresentation
  flat := (pullbackObject' (modulePullbackStabilityOfFinitePresentation B S hS)
    y.1.right (eqToHom (thickeningLift_T_eq hY y).symm)).flat
  properSupport := (pullbackObject' (modulePullbackStabilityOfFinitePresentation B S hS)
    y.1.right (eqToHom (thickeningLift_T_eq hY y).symm)).properSupport
  fibre := (thickeningLiftFibreIso hY y).hom
  isIso_fibre := Iso.isIso_hom _


/-- **A lift of `x` across `A' → A` exists exactly when its module lifts to `X_{A'}`.** -/
theorem nonempty_fiber_iff_nonempty_thickeningLift :
    Nonempty ((Under.post (coherentCFG D).val.p).Fiber (Under.mk (eqToHom hx ≫ T.arrow))) ↔
      Nonempty (D.ThickeningLift x (D.thickeningTestMap hY x hx T)) := by
  refine ⟨fun ⟨y⟩ => ⟨thickeningLiftOfFiber hY y⟩, fun ⟨L⟩ => ?_⟩
  let m : (show (coherentCFG D).val.obj from x) ⟶ (show (coherentCFG D).val.obj from L.toObject) :=
    L.toHom
  exact ⟨⟨Under.mk m, rfl⟩⟩

section Morphism

variable {A₁ A₂ : Type u} [CommRing A₁] [CommRing A₂]
  {T₁ : Deformation.Artin.SquareZeroThickening A B S hS toS hA A₁}
  {T₂ : Deformation.Artin.SquareZeroThickening A B S hS toS hA A₂}

/-- The morphism `Spec A₂' ⟶ Spec A₁'` of objects of the site over `S` of a morphism of
square-zero thickenings `A₁' → A₂'`. -/
def thickeningOverMap (f : Deformation.Artin.SquareZeroThickening.Hom T₁ T₂) :
    (Over.mk T₂.toS' : BigFppfOver B S hS) ⟶ Over.mk T₁.toS' :=
  Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom f.ringHom)))
    (ObjectProperty.hom_ext _ f.overS)

/-- The closed immersions of the two thickenings are compatible with `Spec A₂' ⟶ Spec A₁'`. -/
theorem arrow_comp_thickeningOverMap (f : Deformation.Artin.SquareZeroThickening.Hom T₁ T₂) :
    T₂.arrow ≫ thickeningOverMap f = T₁.arrow := by
  apply Over.OverMorphism.ext
  apply B.inclusion.map_injective
  rw [Over.comp_left, CategoryTheory.Functor.map_comp, T₂.arrow_spec, T₁.arrow_spec]
  change Spec.map (CommRingCat.ofHom T₂.q) ≫ Spec.map (CommRingCat.ofHom f.ringHom) = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, f.overBase]

/-- The morphism `Spec A₂' ⟶ Spec A₁'` of test schemes over a final `Y`. -/
def thickeningTestSchemeMap (f : Deformation.Artin.SquareZeroThickening.Hom T₁ T₂) :
    D.thickeningTestScheme hY T₂ ⟶ D.thickeningTestScheme hY T₁ :=
  CostructuredArrow.homMk (thickeningOverMap f) (hY.hom_ext _ _)

/-- The thickenings of test schemes are compatible with `Spec A₂' ⟶ Spec A₁'`. -/
theorem thickeningTestMap_comp_thickeningTestSchemeMap
    (f : Deformation.Artin.SquareZeroThickening.Hom T₁ T₂) :
    D.thickeningTestMap hY x hx T₂ ≫ D.thickeningTestSchemeMap hY f =
      D.thickeningTestMap hY x hx T₁ := by
  apply CostructuredArrow.hom_ext
  change (eqToHom hx ≫ T₂.arrow) ≫ thickeningOverMap f = eqToHom hx ≫ T₁.arrow
  rw [Category.assoc, arrow_comp_thickeningOverMap]

end Morphism

section Kernel

variable {U : BigFppfOver B S hS} (hU : U = Deformation.Artin.algebraOver A B S hS toS hA)

/-- The identification of `A` with the ring of global functions of a test scheme which is
`Spec A`. -/
def ringEquivOfEq : A ≃+* Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of A)).symm ≪≫
    Scheme.Γ.mapIso
      (eqToIso (congrArg (BigFppfOver.toScheme B S hS).obj hU)).op).commRingCatIsoToRingEquiv

/-- **On global sections, `Spec A ⟶ Spec A'` is `A' → A`**, through `Γ(Spec A') = A'` and the
identification of `A` with the ring of the test scheme. -/
theorem ringEquivOfEq_symm_appTop {A' : Type u} [CommRing A']
    (T : Deformation.Artin.SquareZeroThickening A B S hS toS hA A')
    (z : Γ((BigFppfOver.toScheme B S hS).obj (Over.mk T.toS' : BigFppfOver B S hS), ⊤)) :
    (ringEquivOfEq hU).symm
        (((BigFppfOver.toScheme B S hS).map (eqToHom hU ≫ T.arrow)).appTop z) =
      T.q ((Scheme.ΓSpecIso (CommRingCat.of A')).hom z) := by
  subst hU
  have h1 : ((BigFppfOver.toScheme B S hS).map
      (eqToHom (rfl : Deformation.Artin.algebraOver A B S hS toS hA = _) ≫ T.arrow)) =
      Spec.map (CommRingCat.ofHom T.q) := by
    rw [eqToHom_refl, Category.id_comp]
    exact T.arrow_spec
  rw [h1]
  have h2 := congrArg (fun f => f.hom z) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom T.q))
  simp only at h2
  change (Scheme.ΓSpecIso (CommRingCat.of A)).hom
      ((Scheme.Γ.map (eqToIso (rfl : (BigFppfOver.toScheme B S hS).obj
        (Deformation.Artin.algebraOver A B S hS toS hA) = _)).op.inv).hom
        ((Spec.map (CommRingCat.ofHom T.q)).appTop z)) = _
  simp only [eqToIso_refl]
  exact h2

/-- The test scheme of a square-zero thickening is affine. -/
instance isAffine_thickeningOver {A' : Type u} [CommRing A']
    (T : Deformation.Artin.SquareZeroThickening A B S hS toS hA A') :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (Over.mk T.toS' : BigFppfOver B S hS)) :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of A')))

/-- The kernel of `Γ(Spec A') ⟶ Γ(U)`, as a module over `Γ(U)`. -/
abbrev testKernelModule {A' : Type u} [CommRing A']
    (T : Deformation.Artin.SquareZeroThickening A B S hS toS hA A')
    (hh : Stacks.Thickenings.IsFirstOrderThickening
      ((BigFppfOver.toScheme B S hS).map (eqToHom hU ≫ T.arrow))) :
    ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) :=
  letI := Stacks.Smooth.thickeningKerModule hh
  ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
    (RingHom.ker ((BigFppfOver.toScheme B S hS).map (eqToHom hU ≫ T.arrow)).appTop.hom)

/-- **The kernel of `Γ(Spec A') ⟶ Γ(U)` is the kernel of `A' → A`**, as modules over the ring of
the test scheme, read through the identification of `A` with it. -/
def kernelModuleIso {A' : Type u} [CommRing A']
    (T : Deformation.Artin.SquareZeroThickening A B S hS toS hA A')
    (hh : Stacks.Thickenings.IsFirstOrderThickening
      ((BigFppfOver.toScheme B S hS).map (eqToHom hU ≫ T.arrow))) :
    testKernelModule hU T hh ≅
      (ModuleCat.restrictScalars (ringEquivOfEq hU).symm.toRingHom).obj T.kernel := by
  letI := Stacks.Smooth.thickeningKerModule hh
  letI := Stacks.Smooth.kerModule T.squareZeroSurjection.1 T.squareZeroSurjection.2
  let φ := (Scheme.ΓSpecIso (CommRingCat.of A')).hom.hom
  let ψ := (Scheme.ΓSpecIso (CommRingCat.of A')).inv.hom
  have hφψ : ∀ a, φ (ψ a) = a := (Scheme.ΓSpecIso (CommRingCat.of A')).inv_hom_id_apply
  have hψφ : ∀ z, ψ (φ z) = z := (Scheme.ΓSpecIso (CommRingCat.of A')).hom_inv_id_apply
  have hkey := ringEquivOfEq_symm_appTop hU T
  let g := ((BigFppfOver.toScheme B S hS).map (eqToHom hU ≫ T.arrow)).appTop.hom
  have hmem : ∀ z : RingHom.ker g, φ z.1 ∈ RingHom.ker T.q := fun z => by
    rw [RingHom.mem_ker, ← hkey, show g z.1 = 0 from z.2, map_zero]
  have hmem' : ∀ m : RingHom.ker T.q, ψ m.1 ∈ RingHom.ker g := fun m =>
    RingHom.mem_ker.2 <| (ringEquivOfEq hU).symm.injective <| by
      rw [map_zero]
      change (ringEquivOfEq hU).symm (g (ψ m.1)) = 0
      rw [hkey, hφψ]
      exact m.2
  letI : Module Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) (RingHom.ker T.q) :=
    Module.compHom _ (ringEquivOfEq hU).symm.toRingHom
  refine (LinearEquiv.toModuleIso (X₁ := RingHom.ker g) (X₂ := RingHom.ker T.q)
    { toFun := fun z => (⟨φ z.1, hmem z⟩ : RingHom.ker T.q)
      invFun := fun m => (⟨ψ m.1, hmem' m⟩ : RingHom.ker g)
      left_inv := fun z => Subtype.ext (hψφ z.1)
      right_inv := fun m => Subtype.ext (hφψ m.1)
      map_add' := fun z z' => Subtype.ext (map_add φ z.1 z'.1)
      map_smul' := fun a z => ?_ }) ≪≫ Iso.refl _
  obtain ⟨y, rfl⟩ := Stacks.Smooth.surjective_appTop_of_isFirstOrderThickening hh a
  apply Subtype.ext
  have h1 : (((BigFppfOver.toScheme B S hS).map (eqToHom hU ≫ T.arrow)).appTop.hom y • z :
      RingHom.ker g).1 = y * z.1 := by
    rw [show ((BigFppfOver.toScheme B S hS).map (eqToHom hU ≫ T.arrow)).appTop.hom y • z =
      y • z from Stacks.Smooth.kerModule_smul _ _ y z]
    rfl
  change φ (((BigFppfOver.toScheme B S hS).map (eqToHom hU ≫ T.arrow)).appTop.hom y • z :
      RingHom.ker g).1 = _
  rw [h1, map_mul]
  change φ y * φ z.1 = ((((ringEquivOfEq hU).symm (g y)) • (⟨φ z.1, hmem z⟩ : RingHom.ker T.q) :
    RingHom.ker T.q) : A')
  rw [hkey, Stacks.Smooth.kerModule_smul T.squareZeroSurjection.1
    T.squareZeroSurjection.2 (φ y) ⟨φ z.1, hmem z⟩]
  rfl

/-- **The kernel identification is natural in the thickening**: for a morphism of square-zero
thickenings `f : A₁' → A₂'`, `Γ(Spec A₁') → Γ(Spec A₂')` restricted to the kernels corresponds to
the map `f` induces on the kernels of `A₁' → A` and `A₂' → A`. -/
theorem kernelModuleIso_hom_apply {A₁ A₂ : Type u} [CommRing A₁] [CommRing A₂]
    {T₁ : Deformation.Artin.SquareZeroThickening A B S hS toS hA A₁}
    {T₂ : Deformation.Artin.SquareZeroThickening A B S hS toS hA A₂}
    (f : Deformation.Artin.SquareZeroThickening.Hom T₁ T₂)
    (hh₁ : Stacks.Thickenings.IsFirstOrderThickening
      ((BigFppfOver.toScheme B S hS).map (eqToHom hU ≫ T₁.arrow)))
    (hh₂ : Stacks.Thickenings.IsFirstOrderThickening
      ((BigFppfOver.toScheme B S hS).map (eqToHom hU ≫ T₂.arrow)))
    (z : testKernelModule hU T₁ hh₁) :
    ((kernelModuleIso hU T₂ hh₂).hom
      ⟨((BigFppfOver.toScheme B S hS).map (thickeningOverMap f)).appTop.hom z.1, by
        rw [RingHom.mem_ker, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
          ← CategoryTheory.Functor.map_comp, Category.assoc, arrow_comp_thickeningOverMap]
        exact z.2⟩ : RingHom.ker T₂.q).1 =
      f.ringHom (((kernelModuleIso hU T₁ hh₁).hom z : RingHom.ker T₁.q).1) := by
  change (Scheme.ΓSpecIso (CommRingCat.of A₂)).hom.hom
      (((BigFppfOver.toScheme B S hS).map (thickeningOverMap f)).appTop.hom z.1) =
    f.ringHom ((Scheme.ΓSpecIso (CommRingCat.of A₁)).hom.hom z.1)
  exact congrArg (fun φ => φ.hom z.1) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f.ringHom))

end Kernel

end AlgebraicGeometry.Space.CoherentSituation

end
