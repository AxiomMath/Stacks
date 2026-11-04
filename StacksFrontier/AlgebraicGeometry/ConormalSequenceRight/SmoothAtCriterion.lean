module

public import StacksFrontier.AlgebraicGeometry.ConormalSequenceRight.SchemeShortExact
public import StacksFrontier.AlgebraicGeometry.Smooth.InfinitesimalLifting
public import StacksFrontier.RingTheory.LocalRing.FreeRightExactRank
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkEpiMono
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerShortExact
public import StacksFrontier.AlgebraicGeometry.RelativeDifferentialStalkMap.Scheme
public import StacksFrontier.Topology.Sheaves.Modules.Exactness

/-!
# Smoothness at a point read on the stalk of the conormal sequence

Let `i : Z ⟶ X` be an immersion of schemes over `p : X ⟶ S`. At a point `z` of `Z`, write
`W = i.coborderRange`, `j = i.liftCoborder`, `q = W.ι ≫ p`, and let `R ⟶ A ⟶ C` be the tower of
local rings `𝒪_{S, q (j z)} ⟶ 𝒪_{W, j z} ⟶ 𝒪_{Z, z}` with `J = ker (A ⟶ C)`. The stalk at `z` of
the first arrow `𝒞_{Z/X} ⟶ i^*Ω_{X/S}` of the conormal sequence of [Stacks, Tag 01UZ] is, under
the identifications of the stalks, the map `J/J² ⟶ C ⊗_A Ω_{A/R}` of Mathlib's
`KaehlerDifferential.kerCotangentToTensor`. In particular the two are injective together.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.RegularIdealSheaf
open Stacks.RelativeDifferentialStalkMap
open scoped TensorProduct

universe u

namespace Stacks.ConormalSequenceRight

variable {Z X S : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] (p : X ⟶ S)

/-- **The stalk of the first arrow of the conormal sequence is `kerCotangentToTensor`**, up to
additive identifications of its source and target. -/
theorem exists_addEquiv_stalk_conormalDifferential (z : Z) :
    letI : Algebra (ToType (S.presheaf.stalk
        ((i.coborderRange.ι ≫ p).base (i.liftCoborder.base z))))
        (ToType ((i.coborderRange.toScheme).presheaf.stalk (i.liftCoborder.base z))) :=
      algebraStalkMap (i.coborderRange.ι ≫ p) (i.liftCoborder.base z)
    letI : Algebra (ToType ((i.coborderRange.toScheme).presheaf.stalk (i.liftCoborder.base z)))
        (ToType (Z.presheaf.stalk z)) := (i.liftCoborder.stalkMap z).hom.toAlgebra
    letI : Algebra (ToType (S.presheaf.stalk
        ((i.coborderRange.ι ≫ p).base (i.liftCoborder.base z))))
        (ToType (Z.presheaf.stalk z)) :=
      algebraStalkMap (i.liftCoborder ≫ (i.coborderRange.ι ≫ p)) z
    letI := Scheme.Hom.isScalarTower_stalkMap i.liftCoborder (i.coborderRange.ι ≫ p) z
    ∃ (eL : ToType (TopCat.Presheaf.stalk (C := Ab.{u}) (conormalRetyped i).presheaf z) ≃+
        (RingHom.ker (i.liftCoborder.stalkMap z).hom).Cotangent)
      (Φ : ToType (TopCat.Presheaf.stalk (C := Ab.{u})
          ((Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials p)).val.presheaf z) ≃+
        ToType (Z.presheaf.stalk z) ⊗[ToType ((i.coborderRange.toScheme).presheaf.stalk
          (i.liftCoborder.base z))]
          Ω[ToType ((i.coborderRange.toScheme).presheaf.stalk (i.liftCoborder.base z))⁄
            ToType (S.presheaf.stalk ((i.coborderRange.ι ≫ p).base (i.liftCoborder.base z)))]),
      ∀ m, Φ ((stalkAb Z z).map (conormalDifferential i p) m) =
        KaehlerDifferential.kerCotangentToTensor _ _ _ (eL m) := by
  classical
  set q : i.coborderRange.toScheme ⟶ S := i.coborderRange.ι ≫ p
  let A : Type u := ToType ((i.coborderRange.toScheme).presheaf.stalk (i.liftCoborder.base z))
  let C : Type u := ToType (Z.presheaf.stalk z)
  let R : Type u := ToType (S.presheaf.stalk (q.base (i.liftCoborder.base z)))
  let : Algebra R A := algebraStalkMap q (i.liftCoborder.base z)
  let : Algebra A C := (i.liftCoborder.stalkMap z).hom.toAlgebra
  let : Algebra R C := algebraStalkMap (i.liftCoborder ≫ q) z
  let : IsScalarTower R A C := Scheme.Hom.isScalarTower_stalkMap i.liftCoborder q z
  obtain ⟨eL, heL⟩ := exists_conormalSheafStalkCotangentEquiv i z
  obtain ⟨eM, heMgerm, -⟩ :=
    Scheme.Hom.exists_relativeDifferentialsPullbackStalkEquiv i.liftCoborder q z
  let ψ := ((stalkAb Z z).mapIso (coborderPullbackDifferentialsIso i p)).addCommGroupIsoToAddEquiv
  refine ⟨eL, ψ.symm.trans eM, fun m => ?_⟩
  obtain ⟨V, hz, s, rfl⟩ := exists_germ_unit_eq i z m
  have hcgerm :
      (stalkAb Z z).map (conormalDifferential i p)
          (TopCat.Presheaf.germ (C := Ab.{u}) (conormalRetyped i).presheaf
          (i.liftCoborder ⁻¹ᵁ V) z hz
          (((modulePullbackPushforwardAdjunction i.liftCoborder.toLRSHom.toShHom).unit.app
            ((definingIdeal i).toSheafOfModules)).val.app (op V) s)) =
        (stalkAb Z z).map (coborderPullbackDifferentialsIso i p).hom
          (TopCat.Presheaf.germ (C := Ab.{u})
          ((Scheme.Modules.pullback i.liftCoborder).obj
            (Scheme.Hom.relativeDifferentials q)).val.presheaf (i.liftCoborder ⁻¹ᵁ V) z hz
          (((Scheme.Modules.pullbackPushforwardAdjunction i.liftCoborder).unit.app
            (Scheme.Hom.relativeDifferentials q)).val.app (op V)
            ((Scheme.Hom.universalRelativeDerivation q).d s.1))) := by
    refine Eq.trans (stalkAb_map_germ (conormalDifferential i p) z
      (i.liftCoborder ⁻¹ᵁ V) hz _) ?_
    refine Eq.trans (congrArg (TopCat.Presheaf.germ (C := Ab.{u})
      ((Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials p)).val.presheaf
      (i.liftCoborder ⁻¹ᵁ V) z hz)
      (congrArg (fun m => (m.val.app (op V)).hom s)
        (conormalComparison_comp_conormalDifferential i p))) ?_
    exact (stalkAb_map_germ (coborderPullbackDifferentialsIso i p).hom z
      (i.liftCoborder ⁻¹ᵁ V) hz _).symm
  have h2 : ψ.symm ((stalkAb Z z).map (conormalDifferential i p)
      (TopCat.Presheaf.germ (C := Ab.{u}) (conormalRetyped i).presheaf
        (i.liftCoborder ⁻¹ᵁ V) z hz
        (((modulePullbackPushforwardAdjunction i.liftCoborder.toLRSHom.toShHom).unit.app
          ((definingIdeal i).toSheafOfModules)).val.app (op V) s))) =
      TopCat.Presheaf.germ (C := Ab.{u})
          ((Scheme.Modules.pullback i.liftCoborder).obj
            (Scheme.Hom.relativeDifferentials q)).val.presheaf (i.liftCoborder ⁻¹ᵁ V) z hz
          (((Scheme.Modules.pullbackPushforwardAdjunction i.liftCoborder).unit.app
            (Scheme.Hom.relativeDifferentials q)).val.app (op V)
            ((Scheme.Hom.universalRelativeDerivation q).d s.1)) := by
    rw [hcgerm]
    exact ψ.symm_apply_apply _
  have h5 := KaehlerDifferential.kerCotangentToTensor_toCotangent R A C
    ⟨(i.coborderRange.toScheme).presheaf.germ V (i.liftCoborder.base z) hz s.1,
      germ_mem_ker_stalkMap i.liftCoborder z V hz s⟩
  exact (congrArg eM h2).trans ((heMgerm V hz s.1).trans (h5.symm.trans
    (congrArg (KaehlerDifferential.kerCotangentToTensor R A C) (heL V hz s).symm)))

/-- Changing the base point of a tower of stalks along an equality of morphisms. -/
private theorem subsingleton_h1Cotangent_congr {r r' : Z ⟶ S} (h : r = r') (z : Z) :
    (letI := (r.stalkMap z).hom.toAlgebra;
      Subsingleton (Algebra.H1Cotangent (ToType (S.presheaf.stalk (r.base z)))
        (ToType (Z.presheaf.stalk z)))) ↔
    (letI := (r'.stalkMap z).hom.toAlgebra;
      Subsingleton (Algebra.H1Cotangent (ToType (S.presheaf.stalk (r'.base z)))
        (ToType (Z.presheaf.stalk z)))) := by
  subst h
  rfl

/-- **Smoothness at a point through the conormal sequence.** For an immersion `i : Z ⟶ X` over a
smooth `p : X ⟶ S` with `S` locally Noetherian and `i ≫ p` locally of finite type, `i ≫ p` is
smooth at `z` if and only if the stalk at `z` of the first arrow of the conormal sequence
`𝒞_{Z/X} ⟶ i^*Ω_{X/S} ⟶ Ω_{Z/S} ⟶ 0` is injective and the stalk of `Ω_{Z/S}` is projective. -/
theorem smoothAt_iff_injective_and_projective [IsLocallyNoetherian S] [Smooth p]
    [LocallyOfFiniteType (i ≫ p)] (z : Z) :
    InfinitesimalLifting.SmoothAt (i ≫ p) z ↔
      Function.Injective ((stalkAb Z z).map (conormalDifferential i p)) ∧
        (letI : DecidableEq (OrderDual (TopologicalSpace.OpenNhds z)) := Classical.decEq _;
          Module.Projective (ToType (Z.sheaf.presheaf.stalk z))
            (ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
              (Scheme.Hom.relativeDifferentials (i ≫ p)).val.presheaf z))) := by
  classical
  set q : i.coborderRange.toScheme ⟶ S := i.coborderRange.ι ≫ p with hqdef
  have hr : i.liftCoborder ≫ q = i ≫ p := by
    rw [hqdef, ← Category.assoc, Scheme.Hom.liftCoborder_ι]
  let A : Type u := ToType ((i.coborderRange.toScheme).presheaf.stalk (i.liftCoborder.base z))
  let C : Type u := ToType (Z.presheaf.stalk z)
  let R : Type u := ToType (S.presheaf.stalk (q.base (i.liftCoborder.base z)))
  let : Algebra R A := algebraStalkMap q (i.liftCoborder.base z)
  let : Algebra A C := (i.liftCoborder.stalkMap z).hom.toAlgebra
  let : Algebra R C := algebraStalkMap (i.liftCoborder ≫ q) z
  let : IsScalarTower R A C := Scheme.Hom.isScalarTower_stalkMap i.liftCoborder q z
  have hsurj : Function.Surjective (algebraMap A C) := i.liftCoborder.stalkMap_surjective z
  have : Smooth q := by
    rw [hqdef]
    infer_instance
  have hqfs : AlgebraicGeometry.FormallySmooth q :=
    ((Stacks.Smooth.smooth_iff_locallyOfFinitePresentation_and_formallySmooth q).mp
      inferInstance).2
  have : Algebra.FormallySmooth R A :=
    Scheme.Hom.formallySmooth_stalkMap_of_formallySmooth hqfs (i.liftCoborder.base z)
  obtain ⟨eL, Φ, hΦ⟩ := exists_addEquiv_stalk_conormalDifferential i p z
  have hinj : Function.Injective ((stalkAb Z z).map (conormalDifferential i p)) ↔
      Function.Injective (KaehlerDifferential.kerCotangentToTensor R A C) := by
    have hcomp : ⇑(KaehlerDifferential.kerCotangentToTensor R A C) =
        Φ ∘ (stalkAb Z z).map (conormalDifferential i p) ∘ eL.symm := by
      funext y
      have := hΦ (eL.symm y)
      rw [AddEquiv.apply_symm_apply] at this
      exact this.symm
    rw [hcomp, Φ.injective.of_comp_iff]
    exact (EquivLike.injective_comp eL.symm _).symm
  rw [hinj, Algebra.FormallySmooth.kerCotangentToTensor_injective_iff hsurj]
  refine Iff.trans ?_ (and_congr_left' (subsingleton_h1Cotangent_congr hr z).symm)
  let : Algebra (ToType (S.presheaf.stalk ((i ≫ p).base z))) (ToType (Z.presheaf.stalk z)) :=
    ((i ≫ p).stalkMap z).hom.toAlgebra
  constructor
  · intro h
    have hfs := (Algebra.formallySmooth_iff _ _).1
      (InfinitesimalLifting.SmoothAt.formallySmooth_stalkMap (i ≫ p) z h)
    refine ⟨hfs.2, ?_⟩
    let := algebraStalkMap (i ≫ p) z
    have : Module.Projective (ToType (Z.sheaf.presheaf.stalk z))
        (KaehlerDifferential (ToType (S.presheaf.stalk ((i ≫ p).base z)))
          (ToType (Z.sheaf.presheaf.stalk z))) := hfs.1
    exact Module.Projective.of_equiv (relativeDifferentialsStalkKaehlerEquiv (i ≫ p) z).symm
  · rintro ⟨h1, h2⟩
    have hP : Module.Projective (ToType (Z.presheaf.stalk z))
        (KaehlerDifferential (ToType (S.presheaf.stalk ((i ≫ p).base z)))
          (ToType (Z.presheaf.stalk z))) := by
      let := algebraStalkMap (i ≫ p) z
      have := h2
      have hP' : Module.Projective (ToType (Z.sheaf.presheaf.stalk z))
          (KaehlerDifferential (ToType (S.presheaf.stalk ((i ≫ p).base z)))
            (ToType (Z.sheaf.presheaf.stalk z))) :=
        Module.Projective.of_equiv (relativeDifferentialsStalkKaehlerEquiv (i ≫ p) z)
      exact hP'
    exact InfinitesimalLifting.formallySmooth_stalkMap_smoothAt (i ≫ p) z
      ((Algebra.formallySmooth_iff _ _).2 ⟨hP, h1⟩)

open CategoryTheory.Sheaf in
/-- **Smoothness at a point at constant ranks.** For an immersion `i : Z ⟶ X` over a smooth
`p : X ⟶ S` with `S` locally Noetherian, whose conormal sheaf and `i^*Ω_{X/S}` are finite locally
free of ranks `c` and `d`, the morphism `i ≫ p` is smooth at `z` if and only if `c ≤ d` and the
stalk of `Ω_{Z/S}` at `z` is free of rank `d - c`. -/
theorem smoothAt_iff_nonempty_basis [IsLocallyNoetherian S] [Smooth p]
    [LocallyOfFiniteType (i ≫ p)] (c d : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := toRingCat (Opens.grothendieckTopology ↥Z.toLocallyRingedSpace.toRingedSpace.carrier)
        Z.toLocallyRingedSpace.toRingedSpace.sheaf) (conormalSheaf i : Z.Modules) c]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := toRingCat (Opens.grothendieckTopology ↥Z.toLocallyRingedSpace.toRingedSpace.carrier)
        Z.toLocallyRingedSpace.toRingedSpace.sheaf)
      ((Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials p)) d] (z : Z) :
    InfinitesimalLifting.SmoothAt (i ≫ p) z ↔
      c ≤ d ∧ Nonempty (Module.Basis (Fin (d - c))
        ↑(TopCat.Presheaf.stalk Z.toLocallyRingedSpace.toRingedSpace.sheaf.obj z)
        ↑(TopCat.Presheaf.stalk
          (Scheme.Hom.relativeDifferentials (i ≫ p)).val.presheaf z)) := by
  classical
  let Sc := conormalShortComplex i p
  let f := PresheafOfModules.stalkMapL z (conormalDifferential i p).val
  let g := PresheafOfModules.stalkMapL z Sc.g.val
  have hexact : Function.Exact f g :=
    (ShortComplex.ab_exact_iff_function_exact _).1
      ((AlgebraicGeometry.SheafOfModules.exact_iff_stalkShortComplex_exact
        Z.ringCatSheaf Sc).1 (conormalShortComplex_exact i p) z)
  have hsurj : Function.Surjective g :=
    @Stacks.SheafOfModules.StalkEpiMono.stalk_surjective_of_epi _ _ _ _ Sc.g
      (epi_conormalShortComplex_g i p) z
  obtain ⟨e₁⟩ := Stacks.SheafOfModules.TopWedge.nonempty_stalkLinearEquiv_finsupp
    (X := Z.toLocallyRingedSpace.toRingedSpace.carrier)
    (Osharp := Z.toLocallyRingedSpace.toRingedSpace.sheaf) (conormalSheaf i : Z.Modules) c z
  obtain ⟨e₀⟩ := Stacks.SheafOfModules.TopWedge.nonempty_stalkLinearEquiv_finsupp
    (X := Z.toLocallyRingedSpace.toRingedSpace.carrier)
    (Osharp := Z.toLocallyRingedSpace.toRingedSpace.sheaf)
    ((Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials p)) d z
  have : IsLocalRing ↑(TopCat.Presheaf.stalk Z.toLocallyRingedSpace.toRingedSpace.sheaf.obj z) :=
    Z.toLocallyRingedSpace.isLocalRing z
  rw [smoothAt_iff_injective_and_projective i p z]
  constructor
  · rintro ⟨hinj, hproj⟩
    exact Function.Exact.nonempty_basis_of_injective (Module.Basis.ofRepr e₁)
      (Module.Basis.ofRepr e₀) hexact hsurj hinj hproj
  · rintro ⟨hcd, ⟨b⟩⟩
    exact ⟨Function.Exact.injective_of_basis (Module.Basis.ofRepr e₁) (Module.Basis.ofRepr e₀)
      b hcd hexact hsurj, Module.Projective.of_basis b⟩

end Stacks.ConormalSequenceRight
