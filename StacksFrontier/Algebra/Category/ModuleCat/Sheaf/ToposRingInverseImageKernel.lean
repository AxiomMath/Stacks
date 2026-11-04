module

public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposCommRingImageAdjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackPresentationTransport
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposTerminalSections
import StacksCore.Tactic.StacksAttribute

/-!
# Local surjectivity and the kernel of the inverse image of a sheaf of rings

Let `Φ : Sh(D) ⥤ Sh(C)` be a functor of sheaves of sets, such as the inverse image of a morphism
of topoi, and let `α : R ⟶ R'` be a morphism of sheaves of rings on `D`. Then:

* if `Φ` preserves epimorphisms, `Φ⁻¹α` is locally surjective as soon as `α` is, and
* if `Φ` preserves finite limits and `M ⟶ R` is a kernel of `α`, then `Φ M ⟶ Φ⁻¹R` is a kernel
  of `Φ⁻¹α`.

Here a kernel of `α` is a pullback square of underlying sheaves of sets
```
  M ------→ R
  |         |
  ↓         ↓ α
  ⊤ --0--→  R'
```

## Main results

* `Stacks.Sheaves.ToposPullback.isLocallySurjective_pullbackRingSheafMap` and
  `Stacks.Sheaves.ToposPullback.isLocallySurjective_pullbackCommRingSheafMap`: the inverse image
  of a locally surjective morphism of sheaves of (commutative) rings is locally surjective.
* `Stacks.Sheaves.ToposPullback.isPullback_map_pullbackRingSheafMap` and
  `Stacks.Sheaves.ToposPullback.isPullback_map_pullbackCommRingSheafMap`: the inverse image of a
  kernel square is a kernel square.
* `Stacks.Sheaves.ToposPullback.sections_comp_eq_zero_of_isPullback` and
  `Stacks.Sheaves.ToposPullback.existsUnique_sections_of_isPullback`: the sectionwise form of the
  kernel square.
* `Stacks.Sheaves.ToposPushforward.isLocallySurjective_inverseImageRingFunctor_map`,
  `Stacks.Sheaves.ToposPushforward.isLocallySurjective_inverseImageCommRingFunctor_map` and
  `Stacks.Sheaves.ToposPushforward.isPullback_inverseImageCommRingFunctor_map`: the same
  statements for the inverse image along a morphism of topoi.

## References

* [Stacks Project, Tag 00YV](https://stacks.math.columbia.edu/tag/00YV)
* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 08M4](https://stacks.math.columbia.edu/tag/08M4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Functor Opposite

namespace Stacks.Sheaves.ToposPullback

universe ww ww' vv uu vv' uu'

/-- A morphism of sheaves is locally surjective if its image under `forget₂` is. -/
private theorem isLocallySurjective_of_map_forget₂ {C : Type uu} [Category.{vv} C]
    (J : GrothendieckTopology C) {A B : Type*} [Category A] [Category B]
    {FA : A → A → Type*} {CA : A → Type ww} [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)]
    [ConcreteCategory A FA] {FB : B → B → Type*} {CB : B → Type ww}
    [∀ X Y, FunLike (FB X Y) (CB X) (CB Y)] [ConcreteCategory B FB] [HasForget₂ A B]
    [J.HasSheafCompose (forget₂ A B)] {F G : Sheaf J A} (a : F ⟶ G)
    (h : Presheaf.IsLocallySurjective J ((sheafCompose J (forget₂ A B)).map a).hom) :
    Presheaf.IsLocallySurjective J a.hom := by
  rw [Presheaf.isLocallySurjective_iff_whisker_forget] at h ⊢
  generalize hG : forget A = G
  rw [← HasForget₂.forget_comp (C := A) (D := B)] at hG
  subst hG
  exact h

section EpiLocalSurjectivity

variable {C : Type uu} [Category.{vv} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget RingCat.{ww})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})] [HasSheafify J AddCommGrpCat.{ww}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{ww}]

/-- A morphism of sheaves of rings whose underlying morphism of sheaves of sets is an epimorphism
is locally surjective. -/
theorem isLocallySurjective_of_epi_forgetRing {R R' : Sheaf J RingCat.{ww}} (a : R ⟶ R')
    (h : Epi ((sheafCompose J (forget RingCat.{ww})).map a)) :
    Presheaf.IsLocallySurjective J a.hom := by
  have hb : Epi ((sheafCompose J (forget₂ RingCat.{ww} AddCommGrpCat.{ww})).map a) :=
    (sheafCompose J (forget AddCommGrpCat.{ww})).epi_of_epi_map h
  exact isLocallySurjective_of_map_forget₂ J a
    ((Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{ww}
      ((sheafCompose J (forget₂ RingCat.{ww} AddCommGrpCat.{ww})).map a)).2 hb)

/-- A morphism of sheaves of commutative rings whose underlying morphism of sheaves of sets is an
epimorphism is locally surjective. -/
theorem isLocallySurjective_of_epi_forgetCommRing
    [J.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
    {O O' : Sheaf J CommRingCat.{ww}} (a : O ⟶ O')
    (h : Epi ((sheafCompose J (forget CommRingCat.{ww})).map a)) :
    Presheaf.IsLocallySurjective J a.hom :=
  isLocallySurjective_of_map_forget₂ J a
    (isLocallySurjective_of_epi_forgetRing J
      ((sheafCompose J (forget₂ CommRingCat.{ww} RingCat.{ww})).map a) h)

end EpiLocalSurjectivity

section LocalSurjectivity

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})] [HasSheafify J AddCommGrpCat.{ww}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{ww}]
  (Φ : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)) [PreservesFiniteProducts Φ]
  [Φ.PreservesEpimorphisms]

/-- The inverse image of a locally surjective morphism of sheaves of rings is locally
surjective. -/
theorem isLocallySurjective_pullbackRingSheafMap {R R' : Sheaf K RingCat.{ww'}} (a : R ⟶ R')
    (ha : Presheaf.IsLocallySurjective K a.hom) :
    Presheaf.IsLocallySurjective J (pullbackRingSheafMap J Φ a).hom := by
  have : Sheaf.IsLocallySurjective ((sheafCompose K (forget RingCat.{ww'})).map a) :=
    (Presheaf.isLocallySurjective_iff_whisker_forget K a.hom).1 ha
  refine isLocallySurjective_of_epi_forgetRing J _ ?_
  rw [ringSheafMap_pullbackRingSheafMap]
  exact Φ.map_epi _

end LocalSurjectivity

section LocalSurjectivityCommRing

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  [J.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  [K.HasSheafCompose (forget₂ CommRingCat.{ww'} RingCat.{ww'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})] [HasSheafify J AddCommGrpCat.{ww}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{ww}]
  (Φ : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)) [PreservesFiniteProducts Φ]
  [Φ.PreservesEpimorphisms]

/-- The inverse image of a locally surjective morphism of sheaves of commutative rings is
locally surjective. -/
theorem isLocallySurjective_pullbackCommRingSheafMap {O O' : Sheaf K CommRingCat.{ww'}}
    (a : O ⟶ O') (ha : Presheaf.IsLocallySurjective K a.hom) :
    Presheaf.IsLocallySurjective J (pullbackCommRingSheafMap J Φ a).hom := by
  have : Sheaf.IsLocallySurjective ((sheafCompose K (forget CommRingCat.{ww'})).map a) :=
    (Presheaf.isLocallySurjective_iff_whisker_forget K a.hom).1 ha
  refine isLocallySurjective_of_epi_forgetCommRing J _ ?_
  rw [underlyingRingSheaf_map_pullbackCommRingSheafMap]
  exact Φ.map_epi _

end LocalSurjectivityCommRing

section Kernel

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  (Φ : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)) [PreservesFiniteLimits Φ]

/-- Let `α : R ⟶ R'` be a morphism of sheaves of rings and
let `k : M ⟶ R` exhibit `M` as the kernel of `α` on underlying sheaves of sets, i.e. as the
pullback of the zero section of `R'` along `α`. Then `Φ M` is, in the same sense, the kernel of
the inverse image `Φ⁻¹α`. -/
theorem isPullback_map_pullbackRingSheafMap {R R' : Sheaf K RingCat.{ww'}} (a : R ⟶ R')
    {M : Sheaf K (Type ww')} (k : M ⟶ Sheaf.ringSheaf R)
    (hk : IsPullback k (terminal.from M) ((sheafCompose K (forget RingCat.{ww'})).map a)
      (Sheaf.ringZeroHom R')) :
    IsPullback (Φ.map k) (terminal.from (Φ.obj M))
      ((sheafCompose J (forget RingCat.{ww})).map (pullbackRingSheafMap J Φ a))
      (Sheaf.ringZeroHom (pullbackRingSheaf J Φ R')) := by
  refine (Functor.map_isPullback (F := Φ) hk).of_iso (Iso.refl _) (Iso.refl _)
    (asIso (terminalComparison Φ)) (Iso.refl _) (by simp) ?_ ?_ ?_
  · exact (Category.id_comp _).symm.trans
      (Subsingleton.elim (α := Φ.obj M ⟶ ⊤_ (Sheaf J (Type ww))) _ _)
  · exact (Category.comp_id _).trans ((Category.id_comp _).symm.trans
      (congrArg (fun m ↦ 𝟙 (Φ.obj (Sheaf.ringSheaf R)) ≫ m)
        (ringSheafMap_pullbackRingSheafMap J Φ a).symm))
  · exact (Category.comp_id _).trans ((ringZero_map_aux J Φ R').trans
      (congrArg (fun m ↦ terminalComparison Φ ≫ m) (Category.comp_id _)))

end Kernel

section KernelCommRing

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  [J.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  [K.HasSheafCompose (forget₂ CommRingCat.{ww'} RingCat.{ww'})]
  (Φ : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)) [PreservesFiniteLimits Φ]

/-- Let `α : O ⟶ O'` be a morphism of sheaves of commutative rings and let `k : M ⟶ O` exhibit `M`
as the kernel of `α` on underlying sheaves of sets. Then `Φ M` is, in the same sense, the kernel
of the inverse image `Φ⁻¹α`. -/
theorem isPullback_map_pullbackCommRingSheafMap {O O' : Sheaf K CommRingCat.{ww'}} (a : O ⟶ O')
    {M : Sheaf K (Type ww')}
    (k : M ⟶ Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := K)) O))
    (hk : IsPullback k (terminal.from M)
      ((sheafCompose K (forget RingCat.{ww'})).map ((Stacks.forgetCommRingSheaf K).map a))
      (Sheaf.ringZeroHom ((Stacks.SheafOfModules.Tensor.ringSheaf (J := K)) O'))) :
    IsPullback (Φ.map k) (terminal.from (Φ.obj M))
      ((sheafCompose J (forget RingCat.{ww})).map
        ((Stacks.forgetCommRingSheaf J).map (pullbackCommRingSheafMap J Φ a)))
      (Sheaf.ringZeroHom
        (pullbackRingSheaf J Φ ((Stacks.SheafOfModules.Tensor.ringSheaf (J := K)) O'))) := by
  rw [forgetCommRingSheaf_map_pullbackCommRingSheafMap]
  exact isPullback_map_pullbackRingSheafMap J Φ ((Stacks.forgetCommRingSheaf K).map a) k hk

end KernelCommRing

section KernelSections

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}

/-- A pullback square of types whose bottom left corner is a subsingleton exhibits the top map
as a bijection onto the fibre of the right map over the image of the bottom map. -/
lemma existsUnique_of_isPullback_types {P A T B : Type ww} {fst : P ⟶ A} {snd : P ⟶ T}
    {g : A ⟶ B} {z : T ⟶ B} (h : IsPullback fst snd g z) [Subsingleton T] (t : T) {x : A}
    (hx : g x = z t) :
    ∃! p : P, fst p = x := by
  have hw : (↾fun _ : PUnit.{ww + 1} ↦ x) ≫ g = (↾fun _ : PUnit.{ww + 1} ↦ t) ≫ z := by
    ext _
    exact hx
  refine ⟨h.lift _ _ hw PUnit.unit,
    ConcreteCategory.congr_hom (h.lift_fst _ _ hw) PUnit.unit, fun p hp ↦ ?_⟩
  refine ConcreteCategory.congr_hom
    (h.hom_ext (k := ↾fun _ : PUnit.{ww + 1} ↦ p) (l := h.lift _ _ hw) ?_ ?_) PUnit.unit
  · rw [h.lift_fst]
    ext _
    exact hp
  · rw [h.lift_snd]
    ext _
    exact Subsingleton.elim _ _

variable [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  (Φ : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)) [PreservesFiniteLimits Φ]

/-- In the situation of `Stacks.Sheaves.ToposPullback.isPullback_map_pullbackRingSheafMap`, a
section of the inverse image `Φ⁻¹R` killed by `Φ⁻¹α` comes from a unique section of `Φ M`. -/
theorem existsUnique_sections_of_isPullback {R R' : Sheaf K RingCat.{ww'}} (a : R ⟶ R')
    {M : Sheaf K (Type ww')} (k : M ⟶ Sheaf.ringSheaf R)
    (hk : IsPullback k (terminal.from M) ((sheafCompose K (forget RingCat.{ww'})).map a)
      (Sheaf.ringZeroHom R'))
    (X : Cᵒᵖ) (x : (Sheaf.sectionsFunctor J X).obj (Sheaf.ringSheaf (pullbackRingSheaf J Φ R)))
    (hx : (Sheaf.sectionsFunctor J X).map
        ((sheafCompose J (forget RingCat.{ww})).map (pullbackRingSheafMap J Φ a)) x = 0) :
    ∃! m : (Sheaf.sectionsFunctor J X).obj (Φ.obj M),
      (Sheaf.sectionsFunctor J X).map (Φ.map k) m = x := by
  exact existsUnique_of_isPullback_types (Functor.map_isPullback (F := Sheaf.sectionsFunctor J X)
    (isPullback_map_pullbackRingSheafMap J Φ a k hk)) (Sheaf.terminalSheafSection J X) (x := x)
    (hx.trans (Sheaf.sectionsFunctor_map_ringZeroHom (pullbackRingSheaf J Φ R') X
      (Sheaf.terminalSheafSection J X)).symm)

/-- In the situation of
`Stacks.Sheaves.ToposPullback.isPullback_map_pullbackRingSheafMap`, every section of `Φ M` maps
into the kernel of `Φ⁻¹α`. -/
theorem sections_comp_eq_zero_of_isPullback {R R' : Sheaf K RingCat.{ww'}} (a : R ⟶ R')
    {M : Sheaf K (Type ww')} (k : M ⟶ Sheaf.ringSheaf R)
    (hk : IsPullback k (terminal.from M) ((sheafCompose K (forget RingCat.{ww'})).map a)
      (Sheaf.ringZeroHom R'))
    (X : Cᵒᵖ) (m : (Sheaf.sectionsFunctor J X).obj (Φ.obj M)) :
    (Sheaf.sectionsFunctor J X).map
        ((sheafCompose J (forget RingCat.{ww})).map (pullbackRingSheafMap J Φ a))
      ((Sheaf.sectionsFunctor J X).map (Φ.map k) m) = 0 := by
  have h := congrArg (fun n ↦ (Sheaf.sectionsFunctor J X).map n m)
    (isPullback_map_pullbackRingSheafMap J Φ a k hk).w
  simp only [(Sheaf.sectionsFunctor J X).map_comp_apply] at h
  exact h.trans (Sheaf.sectionsFunctor_map_ringZeroHom (pullbackRingSheaf J Φ R') X _)

end KernelSections

end Stacks.Sheaves.ToposPullback

namespace Stacks.Sheaves.ToposPushforward

open Stacks.Sheaves.ToposPullback

universe ww ww' vv uu vv' uu'

section InverseImage

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  [J.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  [K.HasSheafCompose (forget₂ CommRingCat.{ww'} RingCat.{ww'})]
  (f : MorphismOfTopoi (Sheaf J (Type ww)) (Sheaf K (Type ww')))

omit [J.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  [K.HasSheafCompose (forget₂ CommRingCat.{ww'} RingCat.{ww'})] in
/-- The inverse image of sheaves of rings along a morphism of topoi carries locally surjective
morphisms to locally surjective morphisms. -/
theorem isLocallySurjective_inverseImageRingFunctor_map
    [J.HasSheafCompose (forget AddCommGrpCat.{ww})] [HasSheafify J AddCommGrpCat.{ww}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{ww}]
    {R R' : Sheaf K RingCat.{ww'}} (a : R ⟶ R')
    (ha : Presheaf.IsLocallySurjective K a.hom) :
    Presheaf.IsLocallySurjective J ((inverseImageRingFunctor f).map a).hom :=
  have := Functor.preservesEpimorphisms_of_adjunction f.adj
  isLocallySurjective_pullbackRingSheafMap J f.inverseImage a ha

/-- The inverse image of sheaves of commutative rings along a morphism of topoi carries locally
surjective morphisms to locally surjective morphisms. -/
theorem isLocallySurjective_inverseImageCommRingFunctor_map
    [J.HasSheafCompose (forget AddCommGrpCat.{ww})] [HasSheafify J AddCommGrpCat.{ww}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{ww}]
    {O O' : Sheaf K CommRingCat.{ww'}} (a : O ⟶ O')
    (ha : Presheaf.IsLocallySurjective K a.hom) :
    Presheaf.IsLocallySurjective J ((inverseImageCommRingFunctor f).map a).hom :=
  have := Functor.preservesEpimorphisms_of_adjunction f.adj
  isLocallySurjective_pullbackCommRingSheafMap J f.inverseImage a ha

/-- The kernel of the inverse image of a morphism of sheaves of commutative rings along a
morphism of topoi is the inverse image of the kernel. -/
theorem isPullback_inverseImageCommRingFunctor_map {O O' : Sheaf K CommRingCat.{ww'}}
    (a : O ⟶ O') {M : Sheaf K (Type ww')}
    (k : M ⟶ Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := K)) O))
    (hk : IsPullback k (terminal.from M)
      ((sheafCompose K (forget RingCat.{ww'})).map ((Stacks.forgetCommRingSheaf K).map a))
      (Sheaf.ringZeroHom ((Stacks.SheafOfModules.Tensor.ringSheaf (J := K)) O'))) :
    IsPullback (f.inverseImage.map k) (terminal.from (f.inverseImage.obj M))
      ((sheafCompose J (forget RingCat.{ww})).map
        ((Stacks.forgetCommRingSheaf J).map ((inverseImageCommRingFunctor f).map a)))
      (Sheaf.ringZeroHom
        (pullbackRingSheaf J f.inverseImage
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := K)) O'))) :=
  isPullback_map_pullbackCommRingSheafMap J f.inverseImage a k hk

end InverseImage

end Stacks.Sheaves.ToposPushforward

end
