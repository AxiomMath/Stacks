module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.ColimitsOfHigherDirectImages
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.HigherDirectImageBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Injectives
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Equalizers
public import StacksFrontier.AlgebraicGeometry.Stacks.ColimitsOfCohomologyAbsolute
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactQuasiSeparatedStackAbsolute
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CompositeRightDerivedFunctors
public import StacksFrontier.CategoryTheory.Sites.LocallyBijective
public import StacksFrontier.CategoryTheory.TwoYoneda.RepresentedPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineRefinement

/-!
# Higher direct images along a qcqs morphism commute with filtered colimits (Stacks 0GQW)

Let `f : 𝒳 ⟶ 𝒴` be a quasi-compact and quasi-separated 1-morphism of algebraic stacks and let
`ℱ = colim_i ℱ_i` be a filtered colimit of abelian sheaves on `𝒳`. **Stacks 0GQW** asserts that
`Rᵖf_*ℱ = colim_i Rᵖf_*ℱ_i` for every `p ≥ 0`, in the fppf topology and in the étale topology.

`StacksFrontier/AlgebraicGeometry/Stacks/ColimitsOfHigherDirectImages.lean` proves the
sheafification step of that assertion and takes the local statement — that the cohomology of the
2-fibres of `f` commutes with the colimit — as a hypothesis. This file derives it from
quasi-compactness and quasi-separatedness of `f`, as the source does, and states the tag at the
source's hypotheses.

## Main results

* `AlgebraicGeometry.Stack.preservesColimitsOfShape_rightDerived_abelianDirectImage_fppf_of_qcqs`:
  **Stacks 0GQW**, first assertion, the fppf topology.
* `AlgebraicGeometry.Stack.preservesColimitsOfShape_rightDerived_abelianDirectImage_etale_of_qcqs`:
  **Stacks 0GQW**, second assertion, the étale topology.

On the way:

* `AlgebraicGeometry.Stack.rightDerivedFibreSectionsIso`: the value half of **Stacks 075G** for
  abelian sheaves, `(Rⁿ(ran_f))(y) ≅ Hⁿ((Sch/V) ×_{y, 𝒴} 𝒳, pr⁻¹ -)`, from the base change
  isomorphism of **Stacks 075B** at the terminal object of `Sch/V` and **Stacks 06X1** for `pr`.
* `AlgebraicGeometry.Stack`
  `.isQuasiCompactStack_and_isAbsolutelyQuasiSeparated_twoFibreProduct_objectMorphism`:
  the 2-fibre product over an affine `V` is quasi-compact and quasi-separated.
* `AlgebraicGeometry.Stack.isAbsolutelyQuasiSeparated_schemeStack_of_isAffine`: the stack of an
  affine scheme is quasi-separated in the absolute sense of Stacks 050D part (8).
* `AlgebraicGeometry.Stack.exists_affine_ofArrows_etale`: every object of the étale site of a
  category fibred in groupoids is covered by objects lying over affine schemes.
* `CategoryTheory.Presheaf.isIso_presheafToSheaf_map_of_isIso_app_of_covers`: Stacks 0H6Y for
  covering families indexed in any universe.

## Proof

This is the source's. `Rᵖf_*ℱ` is the sheaf associated to the presheaf
`y ↦ Hᵖ((Sch/V) ×_{y, 𝒴} 𝒳, pr⁻¹ℱ)` (Stacks 075G), and the colimit of sheaves is the sheaf
associated to the presheaf colimit. When `V` is affine the 2-fibre product is quasi-compact and
quasi-separated: its projection to `Sch/V` is a base change of `f`, and `Sch/V` is quasi-compact
and quasi-separated. So Stacks 0GQV applies to `Hᵖ((Sch/V) ×_{y, 𝒴} 𝒳, -)`, and `pr⁻¹` commutes
with all colimits, being a left adjoint. Every object of the site of `𝒴` has a covering by
objects lying over affine schemes, so the comparison map of presheaves, bijective on sections
over those, becomes an isomorphism after sheafification.

The value half of Stacks 075G is obtained in degree zero from the presheaf base change
isomorphism of Stacks 075B for the square of `y` and `f`, evaluated at the terminal object of the
slice `Sch/V`, where right Kan extension along the projection becomes the limit functor. Its
derived form follows because `pr⁻¹` is exact and preserves injectives (Stacks 06X1): `pr` is
faithful, the slice being faithful over the base, and the 2-fibre product, an algebraic stack,
has equalizers (Stacks 06WY).

## Implementation notes

The abelian sheaves take values in `AddCommGrpCat.{u + 1}` and the diagrams are indexed by small
filtered categories at that universe, as in Stacks 0GQV, which is used here.

## References

* [Stacks Project, Tag 0GQW](https://stacks.math.columbia.edu/tag/0GQW)
* [Stacks Project, Tag 0GQV](https://stacks.math.columbia.edu/tag/0GQV)
* [Stacks Project, Tag 075G](https://stacks.math.columbia.edu/tag/075G)
* [Stacks Project, Tag 075B](https://stacks.math.columbia.edu/tag/075B)
* [Stacks Project, Tag 06X1](https://stacks.math.columbia.edu/tag/06X1)
* [Stacks Project, Tag 06WY](https://stacks.math.columbia.edu/tag/06WY)
* [Stacks Project, Tag 0H6Y](https://stacks.math.columbia.edu/tag/0H6Y)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.SiteModules

namespace CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

/-- Over a diagram shape with an initial object `i`, the limit functor is evaluation at `i`. -/
@[simps!]
def limIsoEvaluationOfIsInitial {J : Type u₁} [Category.{v₁} J] {C : Type u₂} [Category.{v₂} C]
    [HasLimitsOfShape J C] {i : J} (hi : IsInitial i) :
    lim (J := J) (C := C) ≅ (evaluation J C).obj i :=
  NatIso.ofComponents
    (fun F => @asIso _ _ _ _ (limit.π F i)
      (IsLimit.isIso_π_app_of_isInitial (limit.isLimit F) i hi))
    (fun α => by simp)

/-- Right Kan extension along `L.op` followed by evaluation at a terminal object of the target is
the limit functor of the source. -/
def ranCompEvaluationIsoLimOfIsTerminal {𝒜 : Type u₁} [Category.{v₁} 𝒜]
    {ℬ : Type u₂} [Category.{v₂} ℬ] {H : Type u₃} [Category.{v₃} H] (L : 𝒜 ⥤ ℬ)
    [∀ G : 𝒜ᵒᵖ ⥤ H, L.op.HasRightKanExtension G]
    [HasLimitsOfShape 𝒜ᵒᵖ H] [HasLimitsOfShape ℬᵒᵖ H] {t : ℬ} (ht : IsTerminal t) :
    L.op.ran ⋙ (evaluation ℬᵒᵖ H).obj (op t) ≅ lim :=
  Functor.isoWhiskerLeft L.op.ran (limIsoEvaluationOfIsInitial ht.op).symm ≪≫ L.op.ranCompLimIso

/-- The first projection of a 2-fibre product over `𝒞` is faithful as soon as the second factor
is faithful over `𝒞`: the second component of a morphism lies over the same base morphism as the
first one. -/
theorem TwoFibreProductOver.faithful_fst_of_faithful_structureFunctor {𝒞 : Type u₁}
    [Category.{v₁} 𝒞]
    {𝒳 : Type u₂} [Category.{v₂} 𝒳] {𝒴 : Type u₃} [Category.{v₃} 𝒴]
    {𝒮 : Type*} [Category* 𝒮] (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (p𝒮 : 𝒮 ⥤ 𝒞)
    (F : 𝒳 ⥤ 𝒮) (G : 𝒴 ⥤ 𝒮) [p𝒴.Faithful] :
    (TwoFibreProductOver.fst p𝒳 p𝒴 p𝒮 F G).Faithful where
  map_injective {P Q} a b h := by
    have ha : a.a = b.a := h
    have hbase : a.hbase = b.hbase := by rw [a.hbase_eq, b.hbase_eq, ha]
    refine TwoFibreProductOver.Hom.ext' ha (p𝒴.map_injective ?_)
    have h₁ := a.hb
    have h₂ := b.hb
    rw [IsHomLift.fac' p𝒴 a.hbase a.b, IsHomLift.fac' p𝒴 b.hbase b.b]
    simp only [hbase]

/-- **Stacks 0H6Y, for covering families indexed in any universe.** A map of presheaves of
abelian groups which is invertible on sections over the members of a family of objects covering
every object of the site becomes an isomorphism after sheafification.

`CategoryTheory.Presheaf.isIso_presheafToSheaf_map_of_hasEnoughObjects_bijective` is the same
statement with the covering families indexed in the morphism universe of the site; the sites of
categories fibred in groupoids over the big fppf site have their covering families indexed one
universe higher. -/
theorem Presheaf.isIso_presheafToSheaf_map_of_isIso_app_of_covers {C : Type u₁}
    [Category.{v₁} C] (J : GrothendieckTopology C) {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{u₂}}
    (φ : P ⟶ Q) [HasWeakSheafify J AddCommGrpCat.{u₂}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u₂}] (Bo : C → Prop)
    (hB : ∀ U : C, ∃ (ι : Type u₃) (V : ι → C) (g : ∀ i, V i ⟶ U),
      (∀ i, Bo (V i)) ∧ Sieve.ofArrows V g ∈ J U)
    (hφ : ∀ ⦃U : C⦄, Bo U → IsIso (φ.app (op U))) :
    IsIso ((presheafToSheaf J AddCommGrpCat.{u₂}).map φ) := by
  have hbij : ∀ ⦃U : C⦄, Bo U → Function.Bijective (φ.app (op U)) := fun U hU =>
    have := hφ hU
    ConcreteCategory.bijective_of_isIso (φ.app (op U))
  have : Presheaf.IsLocallyInjective J φ := ⟨fun {X} x y h => by
    obtain ⟨ι, V, g, hBV, hg⟩ := hB X.unop
    refine J.superset_covering ?_ hg
    rintro W k hk
    obtain ⟨i, a, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hk
    rw [Presheaf.equalizerSieve_apply]
    have key : P.map (g i).op x = P.map (g i).op y := by
      apply (hbij (hBV i)).1
      rw [NatTrans.naturality_apply, NatTrans.naturality_apply, h]
    rw [op_comp, P.map_comp, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, key]⟩
  have : Presheaf.IsLocallySurjective J φ := ⟨fun {U} t => by
    obtain ⟨ι, V, g, hBV, hg⟩ := hB U
    refine J.superset_covering ?_ hg
    rintro W k hk
    obtain ⟨i, a, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hk
    exact (Presheaf.imageSieve φ t).downward_closed ((hbij (hBV i)).2 (Q.map (g i).op t)) a⟩
  rw [← J.W_iff]
  exact J.W_of_isLocallyBijective φ

end CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
/-- A stack equivalent over its base to the stack represented by an object of the site whose
underlying scheme is quasi-separated is quasi-separated over the base. -/
theorem isQuasiSeparatedOver_of_equivalenceOver_yoneda {S₀ : Scheme.{u}} (h₀ : B.Contains S₀)
    (𝒵 : AlgebraicStacks.{u, w} B S₀ h₀) (T : BigFppfOver B S₀ h₀)
    (hT : QuasiSeparatedSpace ((BigFppfOver.toScheme B S₀ h₀).obj T))
    (e : StacksRepresentableCFG.EquivalenceOver 𝒵.val.val.p
      (presheafOfCategories (yoneda.obj T ⋙ typeToCat)).p) :
    IsQuasiSeparatedOver.{u, w} B S₀ h₀ 𝒵 := by
  have hrep := isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S₀ h₀
    (schemeStack.{u, w} B S₀ h₀ (Over.mk (𝟙 (B.obj h₀)))).property
    ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S₀ h₀ T, ⟨e⟩⟩
    (structureMorphism.{u, w} B S₀ h₀ 𝒵).hom
  have hstep : IsQuasiSeparated.{u, u, u + 1} B S₀ h₀
      (structureMorphism.{u, w} B S₀ h₀ 𝒵).hom := by
    refine (hasRelativeProperty_iff_prop_representingMap.{u, u} B S₀ h₀
      (Space.quasiSeparatedProperty B S₀ h₀)
      (structureMorphism.{u, w} B S₀ h₀ 𝒵).hom hrep
      (yoneda.obj T) (yoneda.obj (Over.mk (𝟙 (B.obj h₀))))
      (isAlgebraicSpace_yoneda B S₀ h₀ T)
      (isAlgebraicSpace_yoneda B S₀ h₀ (Over.mk (𝟙 (B.obj h₀))))
      e (PresheafOfCategories.sliceElementsEquivalenceOver _)).2 ?_
    have hk : representingMap B S₀ h₀ 𝒵.val
        (schemeStack.{u, w} B S₀ h₀ (Over.mk (𝟙 (B.obj h₀)))).val
        (yoneda.obj T) (yoneda.obj (Over.mk (𝟙 (B.obj h₀))))
        e (PresheafOfCategories.sliceElementsEquivalenceOver _)
        (structureMorphism.{u, w} B S₀ h₀ 𝒵).hom =
        yoneda.map (Over.mkIdTerminal.from T) :=
      (Over.mkIdTerminal.isTerminalObj yoneda _).hom_ext _ _
    rw [hk]
    have := hT
    exact (Space.isQuasiSeparated_yoneda_map_iff B S₀ h₀ (Over.mkIdTerminal.from T)).2
      inferInstance
  refine (AlgebraicStacks.isQuasiSeparated_iff_isQuasiCompact_relativeDiagonal B S₀ h₀
    (structureMorphism.{u, w} B S₀ h₀ 𝒵) hrep).2 ?_
  exact (isQuasiCompact_relativeDiagonal_iff_isQuasiSeparated B S₀ h₀
    (structureMorphism.{u, w} B S₀ h₀ 𝒵) hrep).2 hstep

/-- **The stack represented by an object of the site with affine underlying scheme is
quasi-separated in the absolute sense of Stacks 050D part (8).** Its view over the terminal scheme
is Construction A of the slice, which is equivalent over the terminal scheme to the slice over the
relocalized object (`AlgebraicGeometry.Stack.factorSliceInverse`), and the underlying scheme of
that object is the same affine scheme. -/
theorem isAbsolutelyQuasiSeparated_schemeStack_of_isAffine (hZ : B.Contains (⊤_ Scheme.{u}))
    (T : BigFppfOver B S hS) (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) :
    AlgebraicStacks.IsAbsolutelyQuasiSeparated.{u, w} B S hS hZ (schemeStack.{u, w} B S hS T) := by
  let g : B.obj hS ⟶ B.obj hZ := ⟨terminal.from S⟩
  obtain ⟨k⟩ := StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence
    (schemeFibredCategory B (⊤_ Scheme.{u}) hZ ((Over.map g).obj T)).isFiberedInGroupoids
    (changeBaseFiberedInGroupoids B S (⊤_ Scheme.{u}) hS hZ g
      (schemeFibredCategory B S hS T)).isFiberedInGroupoids
    (factorSliceInverse B S (⊤_ Scheme.{u}) hS hZ g T).toFunctor
    (factorSliceInverse B S (⊤_ Scheme.{u}) hS hZ g T).w
    (isEquivalence_factorSliceInverse B S (⊤_ Scheme.{u}) hS hZ g T)
  have : IsAffine ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj ((Over.map g).obj T)) := hT
  exact isQuasiSeparatedOver_of_equivalenceOver_yoneda.{u, w} B hZ
    (AlgebraicStacks.viewOverIntegers.{u, w} B S hS hZ (schemeStack.{u, w} B S hS T))
    ((Over.map g).obj T) inferInstance
    (k.symm.trans (PresheafOfCategories.sliceElementsEquivalenceOver _))

/-- **Every object of the associated étale site carries a covering family by affine objects.**
An affine open cover of the scheme underlying the image of the object is, after replacing it by a
tautologically equivalent family inside the chosen size-bounded category of schemes, a selected
étale covering family (open immersions being étale); lifting its members along `p` produces a
covering family for the inherited topology whose members are affine. This is the étale
counterpart of `AlgebraicGeometry.FibredSite.exists_affine_ofArrows`. -/
theorem exists_affine_ofArrows_etale {𝒳 : Type*} [Category* 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids) (W : 𝒳) :
    ∃ (I : Type (u + 1)) (y : I → 𝒳) (φ : ∀ j, y j ⟶ W),
      (∀ j, IsAffineOver B S hS (p.obj (y j))) ∧
        Sieve.ofArrows y φ ∈ BigFppfOver.associatedTopology B S hS p .etale W := by
  classical
  obtain ⟨V, hV, hVU⟩ := exists_isCovering_tautologicallyEquivalent_openCover B
    (p.obj W).left (B.inclusion.obj (p.obj W).left).affineOpenCover.openCover
  have hEt : IsEtaleCovering (⟨(p.obj W).left, V⟩ : Covering B.Schemes) := by
    change (V.map B.inclusion).presieve₀ ∈ Scheme.etalePrecoverage _
    have hU :
        (B.inclusion.obj (p.obj W).left).affineOpenCover.openCover.toPreZeroHypercover.presieve₀
        ∈ Scheme.etalePrecoverage _ :=
      Scheme.precoverage_mono (P := @AlgebraicGeometry.IsOpenImmersion)
        (Q := @AlgebraicGeometry.Etale)
        (fun _ _ _ _ => inferInstance) _
        (B.inclusion.obj (p.obj W).left).affineOpenCover.openCover.mem₀
    refine Precoverage.RespectsIso.of_forall_exists_iso ?_ ?_ hU
    · rintro Z f ⟨i⟩
      obtain ⟨α, hα⟩ := hVU.1
      obtain ⟨e, he⟩ := hα i
      refine ⟨_, e.symm, ?_⟩
      have hef : e.symm.hom ≫ (B.inclusion.obj (p.obj W).left).affineOpenCover.openCover.f i =
          (V.map B.inclusion).f (α i) := by rw [← he, Iso.symm_hom, Iso.inv_hom_id_assoc]
      rw [hef]
      exact ⟨α i⟩
    · rintro Z f ⟨j⟩
      obtain ⟨β, hβ⟩ := hVU.2
      obtain ⟨e, he⟩ := hβ j
      refine ⟨_, e.symm, ?_⟩
      have hef : e.symm.hom ≫ (V.map B.inclusion).f j =
          (B.inclusion.obj (p.obj W).left).affineOpenCover.openCover.f (β j) := by
        rw [← he, Iso.symm_hom, Iso.inv_hom_id_assoc]
      rw [hef]
      exact ⟨β j⟩
  obtain ⟨-, β, hβ⟩ := hVU
  have hVaff : ∀ j, IsAffine (B.inclusion.obj (V.X j)) := by
    intro j
    obtain ⟨e, -⟩ := hβ j
    have : IsAffine
        ((B.inclusion.obj (p.obj W).left).affineOpenCover.openCover.X (β j)) := by
      change IsAffine (Spec ((B.inclusion.obj (p.obj W).left).affineOpenCover.X (β j)))
      exact isAffine_Spec _
    have hIso : IsIso e.hom := e.isIso_hom
    exact @IsAffine.of_isIso _ _ e.hom hIso inferInstance
  let Vobj (j : V.I₀) : BigFppfOver B S hS := Over.mk (V.f j ≫ (p.obj W).hom)
  let vmap (j : V.I₀) : Vobj j ⟶ p.obj W := Over.homMk (V.f j)
  have hBcover : Sieve.ofArrows Vobj vmap ∈
      BigFppfOver.baseOverTopology B S hS .etale (p.obj W) := by
    change Sieve.ofArrows Vobj vmap ∈ ((etaleTopology B).over (B.obj hS)) (p.obj W)
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    change Sieve.ofArrows V.X V.f ∈ etaleTopology B (p.obj W).left
    have hpre : V.presieve₀ ∈ etalePrecoverage B (p.obj W).left := ⟨V, rfl, hV, hEt⟩
    simpa [PreZeroHypercover.presieve₀] using Precoverage.generate_mem_toGrothendieck hpre
  choose y φ hφ using fun j => hp.exists_lift (vmap j) W rfl
  have hdom : ∀ j, p.obj (y j) = Vobj j := fun j => by
    have := hφ j; exact IsHomLift.domain_eq p (vmap j) (φ j)
  have hcart : ∀ j, p.IsStronglyCartesian (p.map (φ j)) (φ j) :=
    fun j => hp.isStronglyCartesian (φ j)
  have hvmapmem : ∀ j, (Sieve.ofArrows (fun k => p.obj (y k)) fun k => p.map (φ k)) (vmap j) := by
    intro j
    refine (Sieve.mem_ofArrows_iff _ _ _).2 ⟨j, eqToHom (hdom j).symm, ?_⟩
    have := hφ j
    have hfac := IsHomLift.fac p (vmap j) (φ j)
    simpa using hfac
  have hfib : p.IsFibered := hp.isFibered
  refine ⟨V.I₀, y, φ, fun j => ?_, ?_⟩
  · change IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj (y j)))
    rw [hdom j]
    exact hVaff j
  · refine (Functor.isInheritedTopology_inheritedTopology p
      (BigFppfOver.baseOverTopology B S hS .etale) y φ hcart).2 ?_
    refine (BigFppfOver.baseOverTopology B S hS .etale).superset_covering ?_ hBcover
    intro Z g hg
    rw [Sieve.mem_ofArrows_iff] at hg
    obtain ⟨j, a, rfl⟩ := hg
    exact (Sieve.ofArrows (fun k => p.obj (y k)) fun k => p.map (φ k)).downward_closed
      (hvmapmem j) a

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (y : 𝒴.val.val.obj)

local notation "𝒜" => twoFibreProductAlgebraicStack B S hS f
    (objectMorphismAlgebraicStacks B S hS 𝒴 y)

/-- **The 2-fibre product `(Sch/V) ×_{y, 𝒴} 𝒳` is quasi-compact and quasi-separated** when `f` is
quasi-compact and quasi-separated and `y` lies over an affine scheme `V`, quasi-separatedness read
absolutely. Its projection to the slice over `V` is a base change of `f`, hence quasi-compact
and quasi-separated, and the slice over an affine scheme is quasi-compact and quasi-separated. -/
theorem isQuasiCompactStack_and_isAbsolutelyQuasiSeparated_twoFibreProduct_objectMorphism
    (hfqc : IsQuasiCompactMorphism.{u, w} B S hS f)
    (hfqs : AlgebraicStacks.IsQuasiSeparated.{u, w} B S hS f)
    (hy : IsAffineObject B S hS 𝒴.val.val.p y) :
    IsQuasiCompactStack.{u, w} B S hS (𝒜).val (𝒜).property ∧
      AlgebraicStacks.IsAbsolutelyQuasiSeparated.{u, w} B S hS B.contains_terminal 𝒜 := by
  have hprojqc : IsQuasiCompactMorphism.{u, w} B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS f
        (objectMorphismAlgebraicStacks B S hS 𝒴 y)).snd :=
    isQuasiCompactMorphism_baseChange B S hS f (objectMorphismAlgebraicStacks B S hS 𝒴 y)
      (twoFibreProductSquareAlgebraicStacks B S hS f
        (objectMorphismAlgebraicStacks B S hS 𝒴 y)).swap
      (Bicategory.isTwoFibreProduct_swap
        (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS f
          (objectMorphismAlgebraicStacks B S hS 𝒴 y))) hfqc
  have hprojqs : AlgebraicStacks.IsQuasiSeparated.{u, w} B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS f
        (objectMorphismAlgebraicStacks B S hS 𝒴 y)).snd :=
    AlgebraicStacks.isQuasiSeparated_baseChange B S hS f _ hfqs
  exact ⟨isQuasiCompactStack_of_isQuasiCompactMorphism B S hS _ hprojqc
      (isQuasiCompactStack_schemeStack_of_isAffine.{u, w} B S hS (𝒴.val.val.p.obj y) hy),
    AlgebraicStacks.isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS B.contains_terminal _
      (isAbsolutelyQuasiSeparated_schemeStack_of_isAffine.{u, w} B S hS B.contains_terminal
        (𝒴.val.val.p.obj y) hy) hprojqs⟩

section Value

local notation "Fn" => CatFiberedInGroupoids.homFunctor f.hom
local notation "Gy" => Functor.TwoYoneda.liftFunctor 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
  (𝒴.val.val.p.obj y) (fibreObj B S hS 𝒴.val y)
local notation "pA" => TwoFibreProductOver.structureFunctor 𝒳.val.val.p
  (Over.forget (𝒴.val.val.p.obj y)) 𝒴.val.val.p (CatFiberedInGroupoids.homFunctor f.hom) Gy
local notation "prX" => TwoFibreProductOver.fst 𝒳.val.val.p
  (Over.forget (𝒴.val.val.p.obj y)) 𝒴.val.val.p (CatFiberedInGroupoids.homFunctor f.hom) Gy
local notation "prV" => TwoFibreProductOver.snd 𝒳.val.val.p
  (Over.forget (𝒴.val.val.p.obj y)) 𝒴.val.val.p (CatFiberedInGroupoids.homFunctor f.hom) Gy

/-- The value at the terminal object of the slice of the 2-Yoneda 1-morphism of `y` is `y`. -/
def liftFunctorObjTerminalIso :
    (Gy).obj (Over.mk (𝟙 (𝒴.val.val.p.obj y))) ≅ y :=
  let L := Functor.TwoYoneda.chosenLift 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
    (𝒴.val.val.p.obj y) (fibreObj B S hS 𝒴.val y) (Over.mk (𝟙 (𝒴.val.val.p.obj y)))
  @asIso _ _ _ _ L.φ (@Functor.IsStronglyCartesian.isIso_of_base_isIso _ _ _ _ 𝒴.val.val.p _ _
    _ _ (𝟙 (𝒴.val.val.p.obj y)) L.φ L.isStronglyCartesian _)

variable (τ : SiteKind)

local notation "JX" => BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ
local notation "JA" => BigFppfOver.associatedTopology B S hS pA τ

/-- The first projection of `(Sch/V) ×_{y, 𝒴} 𝒳` is continuous for the associated topologies. -/
theorem isContinuous_fst_associatedTopology : (prX).IsContinuous JA JX :=
  (BigFppfOver.isContinuous_and_isCocontinuous_associatedTopology B S hS
    (Bicategory.TwoCommSq.fst (twoFibreProductSquareAlgebraicStacks B S hS f
      (objectMorphismAlgebraicStacks B S hS 𝒴 y))).hom τ).1

/-- The first projection of `(Sch/V) ×_{y, 𝒴} 𝒳` is cocontinuous for the associated topologies. -/
theorem isCocontinuous_fst_associatedTopology : (prX).IsCocontinuous JA JX :=
  (BigFppfOver.isContinuous_and_isCocontinuous_associatedTopology B S hS
    (Bicategory.TwoCommSq.fst (twoFibreProductSquareAlgebraicStacks B S hS f
      (objectMorphismAlgebraicStacks B S hS 𝒴 y))).hom τ).2

attribute [local instance] isContinuous_fst_associatedTopology isCocontinuous_fst_associatedTopology

/-- **The value half of Stacks 075G in degree zero.** The sections of the direct image of an
abelian sheaf `ℱ` along `f` over an object `y` of `𝒴` lying over `V` are the global sections of
`pr⁻¹ℱ` on the 2-fibre product `(Sch/V) ×_{y, 𝒴} 𝒳`, naturally in `ℱ`. -/
def fibreSectionsIsoGlobalSections :
    letI := site_hasSheafify_addCommGrp.{u + 1, u, 0} (J := JA)
    fibreSections.{u, 0} B S hS 𝒳.val.val.p Fn τ y ≅
      (prX).sheafPushforwardContinuous AddCommGrpCat.{u + 1} JA JX ⋙
        Sheaf.Γ JA AddCommGrpCat.{u + 1} := by
  letI := site_hasSheafify_addCommGrp.{u + 1, u, 0} (J := JA)
  have e₁ : (Fn).op.ran ⋙ (Functor.whiskeringLeft _ _ AddCommGrpCat.{u + 1}).obj (Gy).op ≅
      (Functor.whiskeringLeft _ _ AddCommGrpCat.{u + 1}).obj (prX).op ⋙ (prV).op.ran :=
    abelianPresheafBaseChangeIso.{u + 1, u, u + 1, u + 1, u + 1, u, u, u, u + 1}
      𝒳.val.val.p (Over.forget (𝒴.val.val.p.obj y))
      𝒴.val.val.p Fn Gy 𝒳.val.isFiberedInGroupoids
      (Functor.IsFiberedInGroupoids.over_forget _) 𝒴.val.isFiberedInGroupoids
      (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
      (Functor.TwoYoneda.liftFunctor_w _ _ _ _)
  have e₂ : (prV).op.ran ⋙ (evaluation _ AddCommGrpCat.{u + 1}).obj
      (op (Over.mk (𝟙 (𝒴.val.val.p.obj y)))) ≅ lim :=
    ranCompEvaluationIsoLimOfIsTerminal (H := AddCommGrpCat.{u + 1}) (prV)
      (Over.mkIdTerminal (X := 𝒴.val.val.p.obj y))
  have e₀ : (evaluation 𝒴.val.val.objᵒᵖ AddCommGrpCat.{u + 1}).obj (op y) ≅
      (evaluation 𝒴.val.val.objᵒᵖ AddCommGrpCat.{u + 1}).obj
        (op ((Gy).obj (Over.mk (𝟙 (𝒴.val.val.p.obj y))))) :=
    (evaluation _ _).mapIso (liftFunctorObjTerminalIso B S hS y).op
  have e₃ := Sheaf.ΓNatIsoLim JA AddCommGrpCat.{u + 1}
  exact Functor.isoWhiskerLeft _ e₀ ≪≫
    Functor.isoWhiskerLeft (sheafToPresheaf JX AddCommGrpCat.{u + 1})
      (Functor.isoWhiskerRight e₁ ((evaluation _ AddCommGrpCat.{u + 1}).obj
        (op (Over.mk (𝟙 _)))) ≪≫ Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ e₂) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((prX).sheafPushforwardContinuousCompSheafToPresheafIso
      AddCommGrpCat.{u + 1} JA JX).symm lim ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft ((prX).sheafPushforwardContinuous AddCommGrpCat.{u + 1} JA JX) e₃.symm

attribute [local instance] Stacks.Cohomology.ColimitsOfCohomology.essentiallySmall_join
  Stacks.Cohomology.ColimitsOfCohomology.hasSheafify_ab_join
  Stacks.Cohomology.ColimitsOfCohomology.enoughInjectives_sheaf_join
  Stacks.Cohomology.ColimitsOfCohomology.globalSections_additive_join

/-- **Stacks 06X1 for the projection `(Sch/V) ×_{y, 𝒴} 𝒳 ⟶ 𝒳`.** Inverse image along the first
projection carries injective abelian sheaves to injective abelian sheaves: the projection is
faithful, the slice over `V` being faithful over the base, and the 2-fibre product is an algebraic
stack, so has equalizers (Stacks 06WY). -/
theorem preservesInjectiveObjects_sheafPushforwardContinuous_fst :
    ((prX).sheafPushforwardContinuous AddCommGrpCat.{u + 1} JA JX).PreservesInjectiveObjects := by
  have : (prX).Faithful :=
    TwoFibreProductOver.faithful_fst_of_faithful_structureFunctor _ _ _ _ _
  have : HasEqualizers (TwoFibreProductOver 𝒳.val.val.p (Over.forget (𝒴.val.val.p.obj y))
      𝒴.val.val.p Fn Gy) :=
    AlgebraicStacks.hasEqualizers B S hS (twoFibreProductAlgebraicStack B S hS f
      (objectMorphismAlgebraicStacks B S hS 𝒴 y))
  exact ⟨fun {I} hI => injective_sheafPushforwardContinuous_obj B S hS pA 𝒳.val.val.p prX
    (B.baseTopology τ) (twoFibreProductAlgebraicStack B S hS f
      (objectMorphismAlgebraicStacks B S hS 𝒴 y)).val.isFiberedInGroupoids
    𝒳.val.isFiberedInGroupoids TwoFibreProductOver.fst_comp_eq I⟩

/-- Inverse image along the first projection of `(Sch/V) ×_{y, 𝒴} 𝒳` is exact. -/
theorem preservesFiniteLimits_sheafPushforwardContinuous_fst :
    PreservesFiniteLimits ((prX).sheafPushforwardContinuous AddCommGrpCat.{u + 1} JA JX) := by
  have := Adjunction.rightAdjoint_preservesLimits.{0, 0}
    ((prX).sheafAdjunctionContinuous AddCommGrpCat.{u + 1} JA JX)
  infer_instance

/-- Inverse image along the first projection of `(Sch/V) ×_{y, 𝒴} 𝒳` preserves all colimits, being
left adjoint to direct image, the projection being cocontinuous. -/
theorem preservesColimits_sheafPushforwardContinuous_fst :
    PreservesColimitsOfSize.{u + 1, u + 1}
      ((prX).sheafPushforwardContinuous AddCommGrpCat.{u + 1} JA JX) :=
  ((prX).sheafAdjunctionCocontinuous AddCommGrpCat.{u + 1} JA JX).leftAdjoint_preservesColimits

/-- **The value half of Stacks 075G.** The `n`-th right derived functor of the sections of the
direct image over `y` is the `n`-th cohomology of the 2-fibre product `(Sch/V) ×_{y, 𝒴} 𝒳` with
coefficients in the inverse image along its projection to `𝒳`, naturally in the abelian sheaf.

The degree-zero identification is `AlgebraicGeometry.Stack.fibreSectionsIsoGlobalSections`. The
inverse image along the projection is exact and preserves injective objects (Stacks 06X1), so it
may be pulled out of the derived functor (Stacks 015Z). -/
def rightDerivedFibreSectionsIso (n : ℕ) :
    letI := site_hasSheafify_addCommGrp.{u + 1, u, 0} (J := JX)
    letI := Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u + 1} JX AddCommGrpCat.{u + 1}
    letI := IsGrothendieckAbelian.enoughInjectives (C := Sheaf JX AddCommGrpCat.{u + 1})
    (fibreSections.{u, 0} B S hS 𝒳.val.val.p Fn τ y).rightDerived n ≅
      (prX).sheafPushforwardContinuous AddCommGrpCat.{u + 1} JA JX ⋙
        (Sheaf.Γ JA AddCommGrpCat.{u + 1}).rightDerived n := by
  letI := site_hasSheafify_addCommGrp.{u + 1, u, 0} (J := JX)
  letI := Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u + 1} JX AddCommGrpCat.{u + 1}
  letI := IsGrothendieckAbelian.enoughInjectives (C := Sheaf JX AddCommGrpCat.{u + 1})
  have := preservesInjectiveObjects_sheafPushforwardContinuous_fst B S hS f y τ
  have := preservesFiniteLimits_sheafPushforwardContinuous_fst B S hS f y τ
  have := preservesColimits_sheafPushforwardContinuous_fst B S hS f y τ
  exact Functor.rightDerivedIsoOfNatIso (fibreSectionsIsoGlobalSections B S hS f y τ) n ≪≫
    Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso _ _ n

end Value

section AffineValue

local notation "Fn" => CatFiberedInGroupoids.homFunctor f.hom
local notation "Gy" => Functor.TwoYoneda.liftFunctor 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
  (𝒴.val.val.p.obj y) (fibreObj B S hS 𝒴.val y)
local notation "pA" => TwoFibreProductOver.structureFunctor 𝒳.val.val.p
  (Over.forget (𝒴.val.val.p.obj y)) 𝒴.val.val.p (CatFiberedInGroupoids.homFunctor f.hom) Gy
local notation "prX" => TwoFibreProductOver.fst 𝒳.val.val.p
  (Over.forget (𝒴.val.val.p.obj y)) 𝒴.val.val.p (CatFiberedInGroupoids.homFunctor f.hom) Gy

attribute [local instance] isContinuous_fst_associatedTopology isCocontinuous_fst_associatedTopology

attribute [local instance] Stacks.Cohomology.ColimitsOfCohomology.essentiallySmall_join
  Stacks.Cohomology.ColimitsOfCohomology.hasSheafify_ab_join
  Stacks.Cohomology.ColimitsOfCohomology.enoughInjectives_sheaf_join
  Stacks.Cohomology.ColimitsOfCohomology.globalSections_additive_join

/-- If the sections functor of the 2-fibre product has derived functors with `colimit.post`
invertible, then so do the derived functors of the sections of the direct image over `y`. -/
private theorem preservesColimitsOfShape_rightDerived_fibreSections_of_isIso_colimit_post
    (τ : SiteKind) (n : ℕ) (I : Type (u + 1)) [SmallCategory I] [IsFiltered I]
    (hΓ : ∀ F : I ⥤ Sheaf (BigFppfOver.associatedTopology B S hS pA τ) AddCommGrpCat.{u + 1},
      IsIso (colimit.post F ((Sheaf.Γ (BigFppfOver.associatedTopology B S hS pA τ)
        AddCommGrpCat.{u + 1}).rightDerived n))) :
    letI := site_hasSheafify_addCommGrp.{u + 1, u, 0}
      (J := BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ)
    letI := Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u + 1}
      (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ) AddCommGrpCat.{u + 1}
    letI := IsGrothendieckAbelian.enoughInjectives
      (C := Sheaf (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ) AddCommGrpCat.{u + 1})
    PreservesColimitsOfShape I
      ((fibreSections.{u, 0} B S hS 𝒳.val.val.p Fn τ y).rightDerived n) := by
  let := site_hasSheafify_addCommGrp.{u + 1, u, 0}
    (J := BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ)
  let := Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u + 1}
    (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ) AddCommGrpCat.{u + 1}
  let := IsGrothendieckAbelian.enoughInjectives
    (C := Sheaf (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ) AddCommGrpCat.{u + 1})
  have : PreservesColimitsOfShape I
      ((Sheaf.Γ (BigFppfOver.associatedTopology B S hS pA τ) AddCommGrpCat.{u + 1}).rightDerived
        n) := ⟨fun {F} => preservesColimit_of_isIso_post _ _⟩
  have := preservesColimits_sheafPushforwardContinuous_fst B S hS f y τ
  exact preservesColimitsOfShape_of_natIso (rightDerivedFibreSectionsIso B S hS f y τ n).symm

/-- **The local statement of Stacks 0GQW, in the fppf topology.** For `f` quasi-compact and
quasi-separated and `y` an object of `𝒴` lying over an affine scheme `V`, the `n`-th derived
functor of the sections of the direct image over `y` commutes with filtered colimits.

It is `Hⁿ((Sch/V) ×_{y, 𝒴} 𝒳, pr⁻¹ -)` by the value half of Stacks 075G,
`AlgebraicGeometry.Stack.rightDerivedFibreSectionsIso`; `pr⁻¹` commutes with all colimits, and
the 2-fibre product is quasi-compact and quasi-separated, so its cohomology commutes with filtered
colimits by Stacks 0GQV. -/
theorem preservesColimitsOfShape_rightDerived_fibreSections_fppf
    (hfqc : IsQuasiCompactMorphism.{u, w} B S hS f)
    (hfqs : AlgebraicStacks.IsQuasiSeparated.{u, w} B S hS f)
    (hy : IsAffineObject B S hS 𝒴.val.val.p y) (n : ℕ)
    (I : Type (u + 1)) [SmallCategory I] [IsFiltered I] :
    letI := site_hasSheafify_addCommGrp.{u + 1, u, 0}
      (J := BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf)
    letI := Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u + 1}
      (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf) AddCommGrpCat.{u + 1}
    letI := IsGrothendieckAbelian.enoughInjectives
      (C := Sheaf (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf) AddCommGrpCat.{u + 1})
    PreservesColimitsOfShape I
      ((fibreSections.{u, 0} B S hS 𝒳.val.val.p Fn .fppf y).rightDerived n) := by
  obtain ⟨hqc, hqs⟩ :=
    isQuasiCompactStack_and_isAbsolutelyQuasiSeparated_twoFibreProduct_objectMorphism
      B S hS f y hfqc hfqs hy
  exact preservesColimitsOfShape_rightDerived_fibreSections_of_isIso_colimit_post B S hS f y .fppf
    n I fun F =>
      isIso_colimit_post_rightDerived_globalSections_fppf_of_isQuasiCompact_absolute.{u, w}
        B S hS (twoFibreProductAlgebraicStack B S hS f (objectMorphismAlgebraicStacks B S hS 𝒴 y))
        hqc hqs n F

/-- **The local statement of Stacks 0GQW, in the étale topology.** For `f` quasi-compact and
quasi-separated and `y` an object of `𝒴` lying over an affine scheme `V`, the `n`-th derived
functor of the sections of the direct image over `y` commutes with filtered colimits.

It is `Hⁿ((Sch/V) ×_{y, 𝒴} 𝒳, pr⁻¹ -)` by the value half of Stacks 075G,
`AlgebraicGeometry.Stack.rightDerivedFibreSectionsIso`; `pr⁻¹` commutes with all colimits, and
the 2-fibre product is quasi-compact and quasi-separated, so its cohomology commutes with filtered
colimits by the étale assertion of Stacks 0GQV. -/
theorem preservesColimitsOfShape_rightDerived_fibreSections_etale
    (hfqc : IsQuasiCompactMorphism.{u, w} B S hS f)
    (hfqs : AlgebraicStacks.IsQuasiSeparated.{u, w} B S hS f)
    (hy : IsAffineObject B S hS 𝒴.val.val.p y) (n : ℕ)
    (I : Type (u + 1)) [SmallCategory I] [IsFiltered I] :
    letI := site_hasSheafify_addCommGrp.{u + 1, u, 0}
      (J := BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .etale)
    letI := Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u + 1}
      (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .etale) AddCommGrpCat.{u + 1}
    letI := IsGrothendieckAbelian.enoughInjectives
      (C := Sheaf (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .etale) AddCommGrpCat.{u + 1})
    PreservesColimitsOfShape I
      ((fibreSections.{u, 0} B S hS 𝒳.val.val.p Fn .etale y).rightDerived n) := by
  obtain ⟨hqc, hqs⟩ :=
    isQuasiCompactStack_and_isAbsolutelyQuasiSeparated_twoFibreProduct_objectMorphism
      B S hS f y hfqc hfqs hy
  exact preservesColimitsOfShape_rightDerived_fibreSections_of_isIso_colimit_post B S hS f y .etale
    n I fun F =>
      isIso_colimit_post_rightDerived_globalSections_etale_of_isQuasiCompact_absolute.{u, w}
        B S hS (twoFibreProductAlgebraicStack B S hS f (objectMorphismAlgebraicStacks B S hS 𝒴 y))
        hqc hqs n F


end AffineValue

section Global

variable (τ : SiteKind)

local notation "Fn" => CatFiberedInGroupoids.homFunctor f.hom
local notation "JX" => BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ
local notation "JY" => BigFppfOver.associatedTopology B S hS 𝒴.val.val.p τ

/-- **The sheafification step of Stacks 0GQW, from the objects lying over affine schemes.** If
every object of the site of `𝒴` is covered by objects lying over affine schemes, and at each such
object `y` the `n`-th derived functor of the sections of the direct image over `y` commutes with
colimits of shape `I`, then so does `Rⁿf_*`.

`Rⁿf_*` is the sheafification of the derived presheaf direct image (the formalized half of Stacks
075G), and sheafification commutes with colimits; the comparison map of presheaves is bijective
on sections over every object lying over an affine scheme, colimits of presheaves being computed
objectwise, so it becomes an isomorphism after sheafification (Stacks 0H6Y). -/
theorem preservesColimitsOfShape_rightDerived_abelianDirectImage_of_isAffineObject (n : ℕ)
    (I : Type (u + 1)) [SmallCategory I]
    (hcov : ∀ W : 𝒴.val.val.obj, ∃ (ι : Type (u + 1)) (V : ι → 𝒴.val.val.obj) (g : ∀ i, V i ⟶ W),
      (∀ i, IsAffineObject B S hS 𝒴.val.val.p (V i)) ∧ Sieve.ofArrows V g ∈ JY W)
    (h : ∀ y : 𝒴.val.val.obj, IsAffineObject B S hS 𝒴.val.val.p y →
      letI := site_hasSheafify_addCommGrp.{u + 1, u, 0} (J := JX)
      letI := Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u + 1} JX AddCommGrpCat.{u + 1}
      letI := IsGrothendieckAbelian.enoughInjectives (C := Sheaf JX AddCommGrpCat.{u + 1})
      PreservesColimitsOfShape I
        ((fibreSections.{u, 0} B S hS 𝒳.val.val.p Fn τ y).rightDerived n)) :
    letI := site_hasSheafify_addCommGrp.{u + 1, u, 0} (J := JX)
    letI := site_hasSheafify_addCommGrp.{u + 1, u, 0} (J := JY)
    letI := Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u + 1} JX AddCommGrpCat.{u + 1}
    letI := IsGrothendieckAbelian.enoughInjectives (C := Sheaf JX AddCommGrpCat.{u + 1})
    letI := abelianDirectImageAdditive.{u, w, 0} B S hS f τ
    PreservesColimitsOfShape I
      (((Fn).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1} JX JY).rightDerived n) := by
  let := site_hasSheafify_addCommGrp.{u + 1, u, 0} (J := JX)
  let := site_hasSheafify_addCommGrp.{u + 1, u, 0} (J := JY)
  let := site_wEqualsLocallyBijective_addCommGrp.{u + 1, u, 0} (J := JY)
  let := Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u + 1} JX AddCommGrpCat.{u + 1}
  let := IsGrothendieckAbelian.enoughInjectives (C := Sheaf JX AddCommGrpCat.{u + 1})
  let := abelianDirectImageAdditive.{u, w, 0} B S hS f τ
  let := ((Fn).op.ranAdjunction AddCommGrpCat.{u + 1}).right_adjoint_additive
  let := (sheafificationAdjunction JX AddCommGrpCat.{u + 1}).right_adjoint_additive
  let P := abelianFibreCohomologyPresheaf.{u, 0} B S hS 𝒳.val.val.p Fn τ n
  have hP : ∀ y : 𝒴.val.val.obj, IsAffineObject B S hS 𝒴.val.val.p y →
      PreservesColimitsOfShape I (P ⋙ (evaluation _ AddCommGrpCat.{u + 1}).obj (op y)) :=
    fun y hy =>
      have := h y hy
      preservesColimitsOfShape_of_natIso
        (Functor.rightDerivedCompIso
          (sheafToPresheaf JX AddCommGrpCat.{u + 1} ⋙ (Fn).op.ran)
          ((evaluation _ AddCommGrpCat.{u + 1}).obj (op y)) n)
  have : PreservesColimitsOfShape I (P ⋙ presheafToSheaf JY AddCommGrpCat.{u + 1}) := by
    constructor
    intro F
    have key : IsIso (colimit.post F (P ⋙ presheafToSheaf JY AddCommGrpCat.{u + 1})) := by
      rw [← colimit.post_post]
      have : IsIso ((presheafToSheaf JY AddCommGrpCat.{u + 1}).map (colimit.post F P)) := by
        refine Presheaf.isIso_presheafToSheaf_map_of_isIso_app_of_covers.{u, u + 1, u + 1, u + 1} JY
          (colimit.post F P)
          (IsAffineObject B S hS 𝒴.val.val.p) hcov fun y hy => ?_
        have := hP y hy
        have hpp := colimit.post_post F P ((evaluation _ AddCommGrpCat.{u + 1}).obj (op y))
        have : IsIso (colimit.post (F ⋙ P) ((evaluation _ AddCommGrpCat.{u + 1}).obj (op y)) ≫
            ((evaluation _ AddCommGrpCat.{u + 1}).obj (op y)).map (colimit.post F P)) :=
          hpp ▸ inferInstance
        exact IsIso.of_isIso_comp_left
          (colimit.post (F ⋙ P) ((evaluation _ AddCommGrpCat.{u + 1}).obj (op y)))
          (((evaluation _ AddCommGrpCat.{u + 1}).obj (op y)).map (colimit.post F P))
      infer_instance
    exact preservesColimit_of_isIso_post _ F
  exact preservesColimitsOfShape_of_natIso
    (abelianHigherDirectImage_iso_sheafify_fibreCohomology.{u, w, 0} B S hS f τ n).symm

end Global

section Main

local notation "Fn" => CatFiberedInGroupoids.homFunctor f.hom

/-- **Stacks 0GQW, first assertion: the fppf topology.** Let `f : 𝒳 ⟶ 𝒴` be a quasi-compact and
quasi-separated 1-morphism of algebraic stacks. Then for every `p ≥ 0` the higher direct image
`Rᵖf_*` of abelian fppf sheaves commutes with filtered colimits:
`Rᵖf_*(colim_i ℱ_i) = colim_i Rᵖf_*ℱ_i`.

The proof is the source's. `Rᵖf_*ℱ` is the sheaf associated to the presheaf
`y ↦ Hᵖ((Sch/V) ×_{y, 𝒴} 𝒳, pr⁻¹ℱ)` (Stacks 075G: the sheafification half is
`AlgebraicGeometry.Stack.abelianHigherDirectImage_iso_sheafify_fibreCohomology`, the value half
`AlgebraicGeometry.Stack.rightDerivedFibreSectionsIso`), and the colimit of sheaves is the sheaf
associated to the presheaf colimit. When `V` is affine the 2-fibre product is quasi-compact and
quasi-separated
(`AlgebraicGeometry.Stack`
`.isQuasiCompactStack_and_isAbsolutelyQuasiSeparated_twoFibreProduct_objectMorphism`),
so Stacks 0GQV applies to its cohomology
(`AlgebraicGeometry.Stack.preservesColimitsOfShape_rightDerived_fibreSections_fppf`), and every
object of the fppf site of `𝒴` has a covering by objects lying over affine schemes
(`AlgebraicGeometry.FibredSite.exists_affine_ofArrows`), which is
`AlgebraicGeometry.Stack`
`.preservesColimitsOfShape_rightDerived_abelianDirectImage_of_isAffineObject`.

Quasi-compactness is Stacks 050U (`AlgebraicGeometry.Stack.IsQuasiCompactMorphism`) and
quasi-separatedness Stacks 04YW (`AlgebraicGeometry.Stack.AlgebraicStacks.IsQuasiSeparated`). The
abelian sheaves take values in `AddCommGrpCat.{u + 1}` and the diagram is indexed by a small
filtered category at that universe, as in Stacks 0GQV. -/
@[stacks 0GQW "first assertion: the fppf topology, for f quasi-compact and quasi-separated"]
theorem preservesColimitsOfShape_rightDerived_abelianDirectImage_fppf_of_qcqs
    (hfqc : IsQuasiCompactMorphism.{u, w} B S hS f)
    (hfqs : AlgebraicStacks.IsQuasiSeparated.{u, w} B S hS f) (n : ℕ)
    (I : Type (u + 1)) [SmallCategory I] [IsFiltered I] :
    letI := site_hasSheafify_addCommGrp.{u + 1, u, 0}
      (J := BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf)
    letI := site_hasSheafify_addCommGrp.{u + 1, u, 0}
      (J := BigFppfOver.associatedTopology B S hS 𝒴.val.val.p .fppf)
    letI := Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u + 1}
      (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf) AddCommGrpCat.{u + 1}
    letI := IsGrothendieckAbelian.enoughInjectives
      (C := Sheaf (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf) AddCommGrpCat.{u + 1})
    letI := abelianDirectImageAdditive.{u, w, 0} B S hS f .fppf
    PreservesColimitsOfShape I
      (((Fn).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
        (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf)
        (BigFppfOver.associatedTopology B S hS 𝒴.val.val.p .fppf)).rightDerived n) :=
  preservesColimitsOfShape_rightDerived_abelianDirectImage_of_isAffineObject B S hS f .fppf n I
    (fun W => FibredSite.exists_affine_ofArrows B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids W)
    (fun y hy => preservesColimitsOfShape_rightDerived_fibreSections_fppf B S hS f y hfqc hfqs hy
      n I)

/-- **Stacks 0GQW, second assertion: the étale topology.** Let `f : 𝒳 ⟶ 𝒴` be a quasi-compact and
quasi-separated 1-morphism of algebraic stacks. Then for every `p ≥ 0` the higher direct image
`Rᵖf_*` of abelian sheaves on the étale sites, taken in the étale topology, commutes with filtered
colimits: `Rᵖf_*(colim_i ℱ_i) = colim_i Rᵖf_*ℱ_i`.

The proof is that of the fppf assertion
`AlgebraicGeometry.Stack.preservesColimitsOfShape_rightDerived_abelianDirectImage_fppf_of_qcqs`,
with the étale assertion of Stacks 0GQV
(`AlgebraicGeometry.Stack.preservesColimitsOfShape_rightDerived_fibreSections_etale`) and the
covering of every object of the étale site of `𝒴` by objects lying over affine schemes
(`AlgebraicGeometry.Stack.exists_affine_ofArrows_etale`). -/
@[stacks 0GQW "second assertion: the étale topology, for f quasi-compact and quasi-separated"]
theorem preservesColimitsOfShape_rightDerived_abelianDirectImage_etale_of_qcqs
    (hfqc : IsQuasiCompactMorphism.{u, w} B S hS f)
    (hfqs : AlgebraicStacks.IsQuasiSeparated.{u, w} B S hS f) (n : ℕ)
    (I : Type (u + 1)) [SmallCategory I] [IsFiltered I] :
    letI := site_hasSheafify_addCommGrp.{u + 1, u, 0}
      (J := BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .etale)
    letI := site_hasSheafify_addCommGrp.{u + 1, u, 0}
      (J := BigFppfOver.associatedTopology B S hS 𝒴.val.val.p .etale)
    letI := Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u + 1}
      (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .etale) AddCommGrpCat.{u + 1}
    letI := IsGrothendieckAbelian.enoughInjectives
      (C := Sheaf (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .etale) AddCommGrpCat.{u + 1})
    letI := abelianDirectImageAdditive.{u, w, 0} B S hS f .etale
    PreservesColimitsOfShape I
      (((Fn).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
        (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .etale)
        (BigFppfOver.associatedTopology B S hS 𝒴.val.val.p .etale)).rightDerived n) :=
  preservesColimitsOfShape_rightDerived_abelianDirectImage_of_isAffineObject B S hS f .etale n I
    (fun W => exists_affine_ofArrows_etale B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids W)
    (fun y hy => preservesColimitsOfShape_rightDerived_fibreSections_etale B S hS f y hfqc hfqs hy
      n I)

end Main

end AlgebraicGeometry.Stack
