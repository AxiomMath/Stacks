module

public import StacksFrontier.Topology.Sheaves.Functors.Pullback.SectionsAndStalks
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackStalkAdjunction
public import StacksFrontier.Topology.Sheaves.Stalk.PullbackUnit
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The underlying abelian sheaf of a module inverse image

Let `f : X ⟶ Y` be a morphism of ringed spaces and `M` a sheaf of `𝒪_Y`-modules. Forgetting the
module structure of the inverse image `f^*M` gives an abelian sheaf on `X`, and so does taking
the topological inverse image of the abelian sheaf underlying `M`. This file constructs the
canonical comparison

`f⁻¹(M^{ab}) ⟶ (f^*M)^{ab}`

and shows that it is an isomorphism whenever every germ map of `f` is invertible — the situation
of the inclusion of a subspace carrying the restricted structure sheaf, where `f^*` is ordinary
restriction. It lets a statement about the topological inverse image of an abelian sheaf be read
as a statement about the module inverse image.

## Main definitions

* `Stacks.RingedSpace.pullbackUnderlyingSheafMap`: the comparison, the adjoint of the underlying
  abelian morphism of the module adjunction unit.

## Main results

* `Stacks.Topology.isIso_stalkComparison_sheafUnit`: the stalk comparison of the unit of
  `TopCat.Sheaf.pullbackPushforwardAdjunction` is an isomorphism, for abelian sheaves.
* `Stacks.Topology.isIso_pullbackHomEquivSymm`: the adjoint `f⁻¹F ⟶ G` of a morphism
  `F ⟶ f_* G` of sheaves is an isomorphism as soon as its stalk comparison is one at every
  point.
* `Stacks.RingedSpace.isIso_pullbackUnderlyingSheafMap`: the comparison is an isomorphism when
  the germ maps of `f` are invertible.

## Implementation notes

Invertibility is read through `Stacks.Sheaves.PullbackUnit.stalkComparison`, the map
`F_{f x} ⟶ G_x` attached to a morphism `F ⟶ f_* G`, rather than through the two stalk maps
separately. That is what makes the direct-image stalk comparison drop out of the argument: by
`Stacks.Sheaves.PullbackUnit.stalkComparison_comp` the construction is compatible with
postcomposition in `G`, so the adjunction identity `η ≫ f_*φ = ψ` becomes a factorisation of
stalk comparisons directly, and no hypothesis on the underlying map of spaces is needed.

`Stacks.Sheaves.PullbackUnit.isIso_stalkComparison` is the unit statement for sheaves of
commutative rings; `isIso_stalkComparison_sheafUnit` is the same argument for abelian sheaves,
which is what the sheaf underlying a sheaf of modules is. Neither is stated for a variable
coefficient category: the identification of the abstract inverse image with "pull back as a
presheaf, then sheafify" is a definitional unfolding of the sheafification instance, and that
instance only reduces once the coefficients are fixed.

On the module side the stalk of `f^*M` is `𝒪_{X,x} ⊗_{𝒪_{Y,f x}} M_{f x}` by [Stacks, Tag 0098],
and `bijective_one_tmul_of_bijective_algebraMap` turns an invertible germ map into bijectivity of
`m ↦ 1 ⊗ₜ m`.

## References

* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 008H](https://stacks.math.columbia.edu/tag/008H)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat
open AlgebraicGeometry RingedSpaceModuleAdjunction

universe u

noncomputable section

namespace Stacks.Topology

section SheafUnit

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

/-- From `a ≫ b = p ≫ t` and `b ≫ c = 𝟙`, conclude `a = p ≫ t ≫ c`. Stated with every object a
variable, like `Stacks.Sheaves.PullbackUnit.isIso_of_comp_eq`: the goals it is applied to mention
the inverse image of a sheaf, on which `rw` cannot build a motive. -/
theorem eq_comp_comp_of_comp_eq {D : Type*} [Category D] {A B E G : D}
    (a : A ⟶ B) (b : B ⟶ E) (c : E ⟶ B) (p : A ⟶ G) (t : G ⟶ E)
    (hab : a ≫ b = p ≫ t) (hbc : b ≫ c = 𝟙 B) : a = p ≫ t ≫ c := by
  rw [← Category.assoc, ← hab, Category.assoc, hbc, Category.comp_id]

/-- Replace the right-hand factor of a composite by an equal composite, keeping a common source.
Stated with every object a variable, for the same reason as `eq_comp_comp_of_comp_eq`. -/
theorem assoc_congr {D : Type*} [Category D] {A B C C' E : D} (a : A ⟶ B)
    (x : B ⟶ C) (y : C ⟶ E) (x' : B ⟶ C') (y' : C' ⟶ E) (h : x ≫ y = x' ≫ y') :
    (a ≫ x) ≫ y = (a ≫ x') ≫ y' := by
  rw [Category.assoc, h, Category.assoc]

/-- Reassociate a fourfold composite. Stated with every object a variable, for the same reason as
`eq_comp_comp_of_comp_eq`. -/
theorem reassoc_four {D : Type*} [Category D] {A B C E G : D}
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ E) (d : E ⟶ G) :
    a ≫ b ≫ c ≫ d = ((a ≫ b) ≫ c) ≫ d := by
  simp only [Category.assoc]

/-- Paste two naturality squares onto a common source. Stated with every object a variable, for
the same reason as `eq_comp_comp_of_comp_eq`. -/
theorem comp_paste_two {D : Type*} [Category D] {A B₁ B₂ C₁ C₂ E G : D}
    (p : A ⟶ B₁) (pk : B₁ ⟶ B₂) (tV : B₂ ⟶ C₂) (cV : C₂ ⟶ E)
    (tW : B₁ ⟶ C₁) (sk : C₁ ⟶ C₂) (cW : C₁ ⟶ G) (qk : G ⟶ E)
    (h₁ : pk ≫ tV = tW ≫ sk) (h₂ : sk ≫ cV = cW ≫ qk) :
    p ≫ pk ≫ tV ≫ cV = (p ≫ tW ≫ cW) ≫ qk := by
  rw [← Category.assoc pk tV cV, h₁, Category.assoc, h₂]
  simp only [Category.assoc]

/-- The unit of the sheaf-level inverse-image adjunction at `F`, followed by the pushforward of
Mathlib's comparison of the two inverse images, is the presheaf-level unit at `F` followed by the
pushforward of the sheafification map of the inverse-image presheaf. -/
theorem sheafPullbackUnit_comp_pullbackIso (F : TopCat.Sheaf AddCommGrpCat.{u} Y) :
    ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app F).hom ≫
        (TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).map
          ((TopCat.Sheaf.pullbackIso AddCommGrpCat.{u} f).hom.app F).hom =
      ((TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app F.presheaf) ≫
        (TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).map
          (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
            (Stacks.Topology.inverseImagePresheaf f F)) := by
  have h := congrArg (fun t => CategoryTheory.InducedCategory.Hom.hom t)
    (Adjunction.unit_leftAdjointUniq_hom_app
      (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f)
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (TopologicalSpace.Opens.map f) AddCommGrpCat.{u} _ _) F)
  exact h

/-- Mathlib's comparison of the two inverse images is invertible as a morphism of presheaves. -/
theorem pullbackIso_hom_comp_inv (F : TopCat.Sheaf AddCommGrpCat.{u} Y) :
    ((TopCat.Sheaf.pullbackIso AddCommGrpCat.{u} f).hom.app F).hom ≫
        (Stacks.Topology.sheafPullbackPresheafIso f F).inv = 𝟙 _ :=
  (Stacks.Topology.sheafPullbackPresheafIso f F).hom_inv_id

/-- **Sections form of the inverse-image adjunction unit:** over an open `U` of the target it is
the presheaf-level unit followed by sheafification and Mathlib's comparison of the two
constructions of the inverse image. -/
theorem sheafPullbackUnit_app (F : TopCat.Sheaf AddCommGrpCat.{u} Y) (U : Opens Y) :
    ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app F).hom.app (op U) =
      ((TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app
          F.presheaf).app (op U) ≫
        (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
            (Stacks.Topology.inverseImagePresheaf f F)).app
          (op ((Opens.map f).obj U)) ≫
        (Stacks.Topology.sheafPullbackPresheafIso f F).inv.app (op ((Opens.map f).obj U)) := by
  have h3 : ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app
          F).hom.app (op U) ≫
        ((TopCat.Sheaf.pullbackIso AddCommGrpCat.{u} f).hom.app F).hom.app
          (op ((Opens.map f).obj U)) =
      ((TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app
          F.presheaf).app (op U) ≫
        (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
            (Stacks.Topology.inverseImagePresheaf f F)).app (op ((Opens.map f).obj U)) := by
    have h := congrArg (fun t => NatTrans.app t (op U))
      (sheafPullbackUnit_comp_pullbackIso f F)
    exact h
  have hcapp : ((TopCat.Sheaf.pullbackIso AddCommGrpCat.{u} f).hom.app F).hom.app
        (op ((Opens.map f).obj U)) ≫
      (Stacks.Topology.sheafPullbackPresheafIso f F).inv.app (op ((Opens.map f).obj U)) = 𝟙 _ := by
    have h := congrArg (fun t => NatTrans.app t (op ((Opens.map f).obj U)))
      (pullbackIso_hom_comp_inv f F)
    exact h
  exact eq_comp_comp_of_comp_eq _ _ _ _ _ h3 hcapp

/-- **The canonical restriction of a section to a subspace is the inverse-image adjunction
unit followed by restriction.** `Stacks.Topology.ambientSection` is built from the presheaf-level
unit and sheafification; this identifies it with the sheaf-level unit, which is the form in which
it meets an adjoint morphism out of the inverse image. -/
theorem ambientSection_eq (F : TopCat.Sheaf AddCommGrpCat.{u} Y) {U : Opens Y} {V : Opens X}
    (h : V ≤ (Opens.map f).obj U) :
    Stacks.Topology.ambientSection f F h =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app
          F).hom.app (op U) ≫
        ((TopCat.Sheaf.pullback AddCommGrpCat.{u} f).obj F).presheaf.map (homOfLE h).op := by
  have t1 := (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
    (Stacks.Topology.inverseImagePresheaf f F)).naturality (homOfLE h).op
  have t2 := (Stacks.Topology.sheafPullbackPresheafIso f F).inv.naturality (homOfLE h).op
  refine Eq.trans ?_ (congrArg (fun z => z ≫
      ((TopCat.Sheaf.pullback AddCommGrpCat.{u} f).obj F).presheaf.map (homOfLE h).op)
    (sheafPullbackUnit_app f F U)).symm
  exact comp_paste_two _ _ _ _ _ _ _ _ t1 t2

/-- **The stalk comparison of the unit of the inverse-image adjunction for sheaves is an
isomorphism.** `TopCat.Sheaf.pullbackIso` identifies the abstract inverse image with the
sheafification of the presheaf inverse image and carries the one unit to the other; the concrete
unit is the presheaf unit followed by sheafification, whose stalk comparison is
`TopCat.Presheaf.stalkPullbackHom` followed by the stalk map of sheafification, and both of those
are isomorphisms. -/
@[ega "0 3.7.2" "special case"]
theorem isIso_stalkComparison_sheafUnit (F : TopCat.Sheaf AddCommGrpCat.{u} Y) (x : X) :
    IsIso (Stacks.Sheaves.PullbackUnit.stalkComparison f AddCommGrpCat.{u}
      ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app F).hom x) := by
  have hunit := sheafPullbackUnit_comp_pullbackIso f F
  have hiso1 : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
        ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).obj F.presheaf))) :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u} _
  have hiso2 : IsIso (TopCat.Presheaf.stalkPullbackHom AddCommGrpCat.{u} f F.presheaf x) :=
    (TopCat.Presheaf.stalkPullbackIso AddCommGrpCat.{u} f F.presheaf x).isIso_hom
  have hiso3 : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((TopCat.Sheaf.pullbackIso AddCommGrpCat.{u} f).hom.app F).hom) :=
    Stacks.Sheaves.PullbackUnit.isIso_stalkFunctor_map_of_iso x AddCommGrpCat.{u}
      (Stacks.Topology.sheafPullbackPresheafIso f F)
  refine Stacks.Sheaves.PullbackUnit.isIso_of_comp_eq _
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((TopCat.Sheaf.pullbackIso AddCommGrpCat.{u} f).hom.app F).hom)
    (TopCat.Presheaf.stalkPullbackHom AddCommGrpCat.{u} f F.presheaf x ≫
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
          ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).obj F.presheaf))) hiso3
    (IsIso.comp_isIso' hiso2 hiso1) ?_
  exact (Stacks.Sheaves.PullbackUnit.stalkComparison_comp f AddCommGrpCat.{u} _ _ x).symm.trans
    ((congrArg (fun t => Stacks.Sheaves.PullbackUnit.stalkComparison f AddCommGrpCat.{u} t x)
        hunit).trans
      (Stacks.Sheaves.PullbackUnit.stalkComparison_comp f AddCommGrpCat.{u} _ _ x))

/-- If `a ≫ b` is an isomorphism and so is `a`, then so is `b`. Stated with the three objects as
variables, like `Stacks.Sheaves.PullbackUnit.isIso_of_comp_eq`, because the goals it is applied
to mention the stalk of a sheaf inverse image, on which `rw` cannot build a motive. -/
theorem isIso_of_comp_eq_right {D : Type*} [Category D] {A B E : D} (a : A ⟶ B) (b : B ⟶ E)
    (c : A ⟶ E) (ha : IsIso a) (hc : IsIso c) (h : a ≫ b = c) : IsIso b := by
  have := ha
  have := hc
  have hb : b = inv a ≫ c := by rw [← h, IsIso.inv_hom_id_assoc]
  rw [hb]
  infer_instance

/-- The unit followed by the pushforward of the adjoint `f⁻¹F ⟶ G` of `ψ : F ⟶ f_* G` is `ψ`. -/
private theorem unit_comp_map_homEquiv_symm {F : TopCat.Sheaf AddCommGrpCat.{u} Y}
    {G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (ψ : F ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj G) :
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app F ≫
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map
        (((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).homEquiv _ _).symm ψ) =
      ψ :=
  (Adjunction.homEquiv_unit _ _ _ _).symm.trans (Equiv.apply_symm_apply _ _)

/-- **Recognising an isomorphism of inverse images.** The adjoint `f⁻¹F ⟶ G` of a morphism
`ψ : F ⟶ f_* G` of sheaves is an isomorphism as soon as the stalk comparison of `ψ` is an
isomorphism at every point. -/
theorem isIso_pullbackHomEquivSymm {F : TopCat.Sheaf AddCommGrpCat.{u} Y}
    {G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (ψ : F ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj G)
    (hψ : ∀ x : X,
      IsIso (Stacks.Sheaves.PullbackUnit.stalkComparison f AddCommGrpCat.{u} ψ.hom x)) :
    IsIso (((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).homEquiv _ _).symm
      ψ) := by
  refine (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso _).2 fun x => ?_
  have hη := isIso_stalkComparison_sheafUnit f F x
  have hψx := hψ x
  have hadj := unit_comp_map_homEquiv_symm f ψ
  refine isIso_of_comp_eq_right
    (Stacks.Sheaves.PullbackUnit.stalkComparison f AddCommGrpCat.{u}
      ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app F).hom x) _
    (Stacks.Sheaves.PullbackUnit.stalkComparison f AddCommGrpCat.{u} ψ.hom x) hη hψx ?_
  refine Eq.trans ?_ (congrArg
    (fun t : F ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj G =>
      Stacks.Sheaves.PullbackUnit.stalkComparison f AddCommGrpCat.{u} t.hom x) hadj)
  exact (Stacks.Sheaves.PullbackUnit.stalkComparison_comp f AddCommGrpCat.{u}
    ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app F).hom
    (((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).homEquiv _ _).symm
      ψ).hom x).symm

end SheafUnit

end Stacks.Topology

namespace Stacks.RingedSpace

/-- Scalar extension along a bijective ring map is bijective on pure tensors with `1`. -/
theorem bijective_one_tmul_of_bijective_algebraMap
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] (h : Function.Bijective (algebraMap R S)) :
    Function.Bijective (fun m : M => (1 : S) ⊗ₜ[R] m) := by
  let e : R ≃ₗ[R] S := LinearEquiv.ofBijective (Algebra.linearMap R S) h
  let t : M ≃ₗ[R] TensorProduct R S M :=
    (TensorProduct.lid R M).symm.trans (TensorProduct.congr e (LinearEquiv.refl R M))
  convert t.bijective using 1
  ext m
  show 1 ⊗ₜ[R] m = (algebraMap R S) 1 ⊗ₜ[R] m
  rw [map_one]

variable {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (f : X ⟶ Y)
  (M : _root_.SheafOfModules.{u} (structureSheafRing Y))

/-- The underlying abelian morphism of the unit of the module inverse-image adjunction. -/
abbrev moduleUnitUnderlying :
    (_root_.SheafOfModules.toSheaf (structureSheafRing Y)).obj M ⟶
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.hom.base).obj
        ((_root_.SheafOfModules.toSheaf (structureSheafRing X)).obj ((modulePullback f).obj M)) :=
  (_root_.SheafOfModules.toSheaf (structureSheafRing Y)).map
    ((modulePullbackPushforwardAdjunction f).unit.app M)

/-- **The stalk comparison of the module inverse-image unit is an isomorphism at a point with
invertible germ map.** The stalk of `f^*M` is `𝒪_{X,x} ⊗_{𝒪_{Y,f x}} M_{f x}` by
[Stacks, Tag 0098], the comparison is `m ↦ 1 ⊗ₜ m` under that identification, and an invertible
germ map makes that bijective. -/
theorem isIso_stalkComparison_moduleUnit (x : X) [IsIso (f.hom.stalkMap x)] :
    IsIso (Stacks.Sheaves.PullbackUnit.stalkComparison f.hom.base AddCommGrpCat.{u}
      (moduleUnitUnderlying f M).hom x) := by
  let : Algebra (Y.presheaf.stalk (f.hom.base x)) (X.presheaf.stalk x) :=
    (f.hom.stalkMap x).hom.toAlgebra
  let M' : PresheafOfModules (Y.presheaf ⋙ forget₂ CommRingCat RingCat) := M.val
  obtain ⟨e, he⟩ := RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv f M x
  refine (ConcreteCategory.isIso_iff_bijective _).2 ?_
  have hb := bijective_one_tmul_of_bijective_algebraMap
    (M := ↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M'.presheaf (f.hom.base x)))
    (ConcreteCategory.bijective_of_isIso (f.hom.stalkMap x))
  have hm : ∀ m : ↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M'.presheaf (f.hom.base x)),
      e ((ConcreteCategory.hom (Stacks.Sheaves.PullbackUnit.stalkComparison f.hom.base
        AddCommGrpCat.{u} (moduleUnitUnderlying f M).hom x)) m) =
      (1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (f.hom.base x)] m := by
    intro m
    obtain ⟨V, hx, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.val.presheaf m
    have key := ConcreteCategory.congr_hom
      (Stacks.Sheaves.PullbackUnit.germ_stalkComparison f.hom.base AddCommGrpCat.{u}
        (moduleUnitUnderlying f M).hom x V hx) s
    exact (congrArg e key).trans (he V hx s)
  refine ⟨fun a b h => hb.1 ((hm a).symm.trans ((congrArg e h).trans (hm b))), fun m => ?_⟩
  obtain ⟨n, hn⟩ := hb.2 (e m)
  exact ⟨n, e.injective ((hm n).trans hn)⟩

/-- **The comparison from the inverse image of the underlying abelian sheaf to the underlying
abelian sheaf of the module inverse image**: the adjoint of the underlying abelian morphism of
the module adjunction unit. -/
def pullbackUnderlyingSheafMap :
    (TopCat.Sheaf.pullback AddCommGrpCat.{u} f.hom.base).obj
        ((_root_.SheafOfModules.toSheaf (structureSheafRing Y)).obj M) ⟶
      (_root_.SheafOfModules.toSheaf (structureSheafRing X)).obj ((modulePullback f).obj M) :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f.hom.base).homEquiv _ _).symm
    (moduleUnitUnderlying f M)

/-- The comparison is adjoint to the underlying abelian morphism of the module adjunction
unit. -/
theorem pullbackUnderlyingSheafMap_fac :
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f.hom.base).unit.app
        ((_root_.SheafOfModules.toSheaf (structureSheafRing Y)).obj M) ≫
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.hom.base).map
        (pullbackUnderlyingSheafMap f M) =
    moduleUnitUnderlying f M :=
  Stacks.Topology.unit_comp_map_homEquiv_symm f.hom.base (moduleUnitUnderlying f M)

/-- **The underlying abelian sheaf of a module inverse image is the inverse image of the
underlying abelian sheaf**, for a morphism of ringed spaces all of whose germ maps are
invertible. This is the Stacks Project's "`i^* = i^{-1}` for the inclusion of a subspace with the
restricted structure sheaf". -/
theorem isIso_pullbackUnderlyingSheafMap (hs : ∀ x : X, IsIso (f.hom.stalkMap x)) :
    IsIso (pullbackUnderlyingSheafMap f M) := by
  refine Stacks.Topology.isIso_pullbackHomEquivSymm f.hom.base _ fun x => ?_
  have := hs x
  exact isIso_stalkComparison_moduleUnit f M x

end Stacks.RingedSpace

end

end
