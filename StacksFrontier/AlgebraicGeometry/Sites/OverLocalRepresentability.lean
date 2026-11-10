module

public import Mathlib.AlgebraicGeometry.Sites.Representability
public import Mathlib.CategoryTheory.Sites.Over
public import StacksFrontier.AlgebraicGeometry.Topologies.FpqcQuasicoherentReduction

/-!
# Local representability for presheaves on schemes over a base

A Zariski sheaf of sets on the schemes over `S` which is covered, at every point with values in a
field, by representable subfunctors whose inclusions are representable by open immersions is
itself representable. This is the shape of Stacks Tag 01JJ used for functors on `Over S`.

## Main definitions

* `Stacks.Sites.totalSubfunctor`: the subfunctor of the total presheaf
  `Stacks.Sites.totalPresheaf P` cut out by a subfunctor of `P`.
* `Stacks.Sites.totalPresheafRepresentableBy`: the total presheaf of a representable presheaf on
  `CategoryTheory.Over X` is representable by the underlying object.
* `Stacks.Sites.representableByOfTotalPresheaf`: conversely, a representation of the total
  presheaf gives a representation on `CategoryTheory.Over X`.

## Main results

* `Stacks.Sites.presheaf_subfunctor_ι_of_factor` and
  `Stacks.Sites.exists_factor_of_presheaf_subfunctor_ι`: the inclusion of a subfunctor has a
  relative property `P` exactly when its pullbacks are cut out by morphisms with `P`.
* `AlgebraicGeometry.isOpenImmersion_over_presheaf_subfunctor_ι_of_openLocus` and
  `AlgebraicGeometry.exists_openLocus_of_isOpenImmersion_over_presheaf`: a subfunctor of a
  presheaf on the schemes over `S` is open exactly when every section has an open locus.
* `AlgebraicGeometry.isRepresentable_of_isOpenImmersion_subfunctors`: **local
  representability on `Over S`.**

## Implementation notes

The criterion is reduced to Mathlib's
`AlgebraicGeometry.Scheme.LocalRepresentability.isRepresentable`, which is stated for presheaves
on the category of all schemes, by passing to the total presheaf
`T ↦ Σ a : T ⟶ S, F (T, a)`. Being a Zariski sheaf transfers by
`Stacks.Sites.isSheaf_over_iff_isSheaf_totalPresheaf`; an open subfunctor `G` of `F` gives the
open subfunctor `Stacks.Sites.totalSubfunctor G` of the total presheaf, which is represented by
the underlying scheme of the representing object of `G`; and joint surjectivity is checked at the
residue fields, where the open loci of the charts are seen to cover. Representability of the total
presheaf is transported back by `Stacks.Sites.representableByOfTotalPresheaf`.

The statement is not registered as Stacks 01JJ: that lemma is about functors on all schemes, and
its version on `Over S` is the theorem below; Mathlib's statement carries the tag.

## References

* [Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace Stacks.Sites

section General

variable {C : Type u} [Category.{v} C]

/-- **A subfunctor whose pullbacks are cut out by monomorphisms with a property `P`.** If for
every section `s` of `F` over `T` there is a monomorphism `j : U ⟶ T` with `P j` such that the
restriction of `s` along `e : T' ⟶ T` lies in `G` exactly when `e` factors through `j`, then the
inclusion of `G` into `F` is a morphism of presheaves with the relative property `P`. -/
theorem presheaf_subfunctor_ι_of_factor (P : MorphismProperty C) [P.RespectsIso]
    {F : Cᵒᵖ ⥤ Type v} (G : Subfunctor F)
    (h : ∀ (T : C) (s : F.obj (op T)), ∃ (U : C) (j : U ⟶ T), Mono j ∧ P j ∧
      ∀ (T' : C) (e : T' ⟶ T), F.map e.op s ∈ G.obj (op T') ↔ ∃ l : T' ⟶ U, l ≫ j = e) :
    P.presheaf G.ι := by
  refine MorphismProperty.relative.of_exists fun T g => ?_
  obtain ⟨U, j, hj, hP, hU⟩ := h T (yonedaEquiv g)
  let fst : yoneda.obj U ⟶ G.toFunctor :=
    { app := fun T' => ↾fun l => ⟨F.map (l ≫ j).op (yonedaEquiv g), (hU _ _).2 ⟨l, rfl⟩⟩
      naturality := by
        intro T₁ T₂ k
        ext l
        apply Subtype.ext
        change F.map ((k.unop ≫ l) ≫ j).op (yonedaEquiv g) =
          F.map k (F.map (l ≫ j).op (yonedaEquiv g))
        rw [← Functor.map_comp_apply, Category.assoc, op_comp]
        rfl }
  refine ⟨U, fst, j, ?_, hP⟩
  apply IsPullback.of_forall_isPullback_app
  intro T'
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · ext l
    change F.map (l ≫ j).op (yonedaEquiv g) = g.app T' (l ≫ j)
    exact map_yonedaEquiv g (l ≫ j)
  · rintro l₁ l₂ ⟨-, h₂⟩
    exact (cancel_mono j).1 h₂
  · intro x e hx
    change x.1 = g.app T' e at hx
    have hmem : F.map e.op (yonedaEquiv g) ∈ G.obj T' := by
      rw [map_yonedaEquiv, ← hx]
      exact x.2
    obtain ⟨l, hl⟩ := (hU T'.unop e).1 hmem
    refine ⟨l, Subtype.ext ?_, hl⟩
    change F.map (l ≫ j).op (yonedaEquiv g) = x.1
    rw [hl, map_yonedaEquiv, hx]

/-- **The pullbacks of a subfunctor with a relative property are cut out by morphisms with that
property.** Conversely to `Stacks.Sites.presheaf_subfunctor_ι_of_factor`, if the inclusion of `G`
into `F` has the relative property `P`, then for every section `s` of `F` over `T` there is a
morphism `j : U ⟶ T` with `P j` such that the restriction of `s` along `e : T' ⟶ T` lies in `G`
exactly when `e` factors through `j`. -/
theorem exists_factor_of_presheaf_subfunctor_ι {P : MorphismProperty C}
    {F : Cᵒᵖ ⥤ Type v} {G : Subfunctor F} (hG : P.presheaf G.ι) (T : C) (s : F.obj (op T)) :
    ∃ (U : C) (j : U ⟶ T), P j ∧
      ∀ (T' : C) (e : T' ⟶ T), F.map e.op s ∈ G.obj (op T') ↔ ∃ l : T' ⟶ U, l ≫ j = e := by
  let g : yoneda.obj T ⟶ F := yonedaEquiv.symm s
  refine ⟨hG.rep.pullback g, hG.rep.snd g, hG.property_snd g, fun T' e => ⟨fun he => ?_, ?_⟩⟩
  · obtain ⟨l, -, hl⟩ := Types.exists_of_isPullback ((hG.rep.isPullback g).map
      ((evaluation _ _).obj (op T'))) (⟨F.map e.op s, he⟩ : G.toFunctor.obj (op T')) e rfl
    exact ⟨l, hl⟩
  · rintro ⟨l, rfl⟩
    have hw := congrArg (fun η => η.app (op T') l) (hG.rep.isPullback g).w
    change ((hG.rep.fst g).app (op T') l).1 = g.app (op T') (l ≫ hG.rep.snd g) at hw
    change g.app (op T') (l ≫ hG.rep.snd g) ∈ G.obj (op T')
    rw [← hw]
    exact ((hG.rep.fst g).app (op T') l).2

end General

section Total

variable {C : Type u} [Category.{v} C] {X : C}

/-- Two elements of the total presheaf of a representable presheaf, given by morphisms to the
representing object with the same underlying morphism, agree. -/
lemma totalPresheaf_sigma_eq_of_left_eq {P : (Over X)ᵒᵖ ⥤ Type v} {A : Over X}
    (R : P.RepresentableBy A) {T : C} {f g : T ⟶ X} (hfg : f = g) (m : Over.mk f ⟶ A)
    (n : Over.mk g ⟶ A) (h : m.left = n.left) :
    (⟨f, R.homEquiv m⟩ : (totalPresheaf P).obj (op T)) = ⟨g, R.homEquiv n⟩ := by
  subst hfg
  obtain rfl : m = n := Over.OverMorphism.ext h
  rfl

/-- **The total presheaf of a representable presheaf on `CategoryTheory.Over X` is represented
by the underlying object of the representing object.** -/
def totalPresheafRepresentableBy {P : (Over X)ᵒᵖ ⥤ Type v} {A : Over X}
    (R : P.RepresentableBy A) : (totalPresheaf P).RepresentableBy A.left where
  homEquiv {T} :=
    { toFun k := ⟨k ≫ A.hom, R.homEquiv (Over.homMk k rfl)⟩
      invFun x := (R.homEquiv.symm x.2).left
      left_inv k := by simp
      right_inv x := by
        obtain ⟨f, s⟩ := x
        refine (totalPresheaf_sigma_eq_of_left_eq R (Over.w (R.homEquiv.symm s)) _
          (R.homEquiv.symm s) rfl).trans ?_
        rw [Equiv.apply_symm_apply]
        rfl }
  homEquiv_comp {T T'} g k := by
    change (⟨(g ≫ k) ≫ A.hom, _⟩ : (totalPresheaf P).obj (op T)) =
      totalPresheafMap P g.op ⟨k ≫ A.hom, R.homEquiv (Over.homMk k rfl)⟩
    rw [totalPresheafMap_mk P g.op (c := (g ≫ k) ≫ A.hom) (Category.assoc _ _ _).symm,
      ← R.homEquiv_comp]
    exact totalPresheaf_sigma_eq_of_left_eq R rfl _ _ (by simp)

/-- The restriction of the universal element of a representation of the total presheaf along the
underlying morphism of a morphism of `CategoryTheory.Over X`. -/
lemma totalPresheaf_homEquiv_left {P : (Over X)ᵒᵖ ⥤ Type v} {W : C}
    (R : (totalPresheaf P).RepresentableBy W) {B : Over X}
    (k : B ⟶ Over.mk (R.homEquiv (𝟙 W)).1) :
    R.homEquiv k.left = ⟨B.hom, P.map k.op (R.homEquiv (𝟙 W)).2⟩ := by
  rw [R.homEquiv_eq]
  change totalPresheafMap P k.left.op ⟨(R.homEquiv (𝟙 W)).1, (R.homEquiv (𝟙 W)).2⟩ = _
  exact totalPresheafMap_mk P k.left.op (Over.w k) _

/-- **Representability of the total presheaf implies representability on
`CategoryTheory.Over X`.** The representing object is the representing object of the total
presheaf, with the first component of the universal element as structure morphism. -/
def representableByOfTotalPresheaf {P : (Over X)ᵒᵖ ⥤ Type v} {W : C}
    (R : (totalPresheaf P).RepresentableBy W) :
    P.RepresentableBy (Over.mk (R.homEquiv (𝟙 W)).1) where
  homEquiv {B} := Equiv.ofBijective (fun k => P.map k.op (R.homEquiv (𝟙 W)).2) <| by
    refine ⟨fun k₁ k₂ h => ?_, fun y => ?_⟩
    · apply Over.OverMorphism.ext
      apply R.homEquiv.injective
      rw [totalPresheaf_homEquiv_left, totalPresheaf_homEquiv_left]
      exact congrArg (fun z => (⟨B.hom, z⟩ : (totalPresheaf P).obj (op B.left))) h
    · have hk := R.homEquiv.apply_symm_apply (⟨B.hom, y⟩ : (totalPresheaf P).obj (op B.left))
      have hb : R.homEquiv.symm ⟨B.hom, y⟩ ≫ (R.homEquiv (𝟙 W)).1 = B.hom :=
        congrArg Sigma.fst ((R.homEquiv_eq _).symm.trans hk)
      refine ⟨Over.homMk (R.homEquiv.symm ⟨B.hom, y⟩) hb, ?_⟩
      have h := (totalPresheaf_homEquiv_left R
        (Over.homMk (R.homEquiv.symm ⟨B.hom, y⟩) hb : B ⟶ _)).symm.trans
          ((congrArg R.homEquiv (Over.homMk_left _ _)).trans hk)
      exact eq_of_heq (Sigma.mk.inj_iff.1 h).2
  homEquiv_comp g k := by
    change P.map (g ≫ k).op _ = P.map g.op (P.map k.op _)
    rw [op_comp, Functor.map_comp_apply]

/-- **Representability of the total presheaf implies representability on
`CategoryTheory.Over X`.** -/
theorem isRepresentable_of_isRepresentable_totalPresheaf {P : (Over X)ᵒᵖ ⥤ Type v}
    (h : (totalPresheaf P).IsRepresentable) : P.IsRepresentable :=
  (representableByOfTotalPresheaf h.has_representation.choose_spec.some).isRepresentable

/-- The subfunctor of the total presheaf cut out by a subfunctor `G` of `P`: the pairs whose
second component lies in `G`. -/
@[simps]
def totalSubfunctor {P : (Over X)ᵒᵖ ⥤ Type v} (G : Subfunctor P) :
    Subfunctor (totalPresheaf P) where
  obj _T := {x | x.2 ∈ G.obj (op (Over.mk x.1))}
  map _h _x hx := G.map _ hx

/-- The total subfunctor of `G` is the total presheaf of `G`. -/
def totalSubfunctorIso {P : (Over X)ᵒᵖ ⥤ Type v} (G : Subfunctor P) :
    (totalSubfunctor G).toFunctor ≅ totalPresheaf G.toFunctor :=
  NatIso.ofComponents (fun T =>
    { hom := ↾fun x => ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
      inv := ↾fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩ }) (fun _ => rfl)

end Total

end Stacks.Sites

namespace AlgebraicGeometry

open Stacks.Sites

/-- Being an open immersion on the underlying schemes respects isomorphisms of schemes over
`S`. -/
theorem isOpenImmersion_over_respectsIso (S : Scheme.{u}) :
    (IsOpenImmersion.over (X := S)).RespectsIso := by
  rw [MorphismProperty.over_eq_inverseImage]
  infer_instance

/-- A morphism over `S` factors through an open immersion over `S` exactly when its underlying
morphism lands in the range of the open immersion. -/
private theorem exists_comp_eq_iff_range_subset {S : Scheme.{u}} {V T T' : Over S} (j : V ⟶ T)
    [IsOpenImmersion j.left] (g : T' ⟶ T) :
    (∃ l : T' ⟶ V, l ≫ j = g) ↔ Set.range g.left ⊆ Set.range j.left := by
  constructor
  · rintro ⟨l, rfl⟩ _ ⟨x, rfl⟩
    exact ⟨l.left x, rfl⟩
  · intro hg
    refine ⟨Over.homMk (IsOpenImmersion.lift j.left g.left hg) ?_, ?_⟩
    · rw [← Over.w j, IsOpenImmersion.lift_fac_assoc]
      exact Over.w g
    · ext
      exact IsOpenImmersion.lift_fac _ _ _

/-- **An open subfunctor described by open loci.** Let `G` be a subfunctor of a presheaf `F` on
the schemes over `S`. Suppose that for every section `s` of `F` over `T` there is an open `U` of
`T` such that the restriction of `s` along `g : T' ⟶ T` lies in `G` exactly when `g` lands in
`U`. Then the inclusion of `G` into `F` is representable by open immersions. -/
theorem isOpenImmersion_over_presheaf_subfunctor_ι_of_openLocus {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u} (G : Subfunctor F)
    (h : ∀ (T : Over S) (s : F.obj (op T)), ∃ U : T.left.Opens, ∀ (T' : Over S) (g : T' ⟶ T),
      F.map g.op s ∈ G.obj (op T') ↔ Set.range g.left ⊆ U) :
    (IsOpenImmersion.over (X := S)).presheaf G.ι := by
  have := isOpenImmersion_over_respectsIso S
  refine presheaf_subfunctor_ι_of_factor _ G fun T s => ?_
  obtain ⟨U, hU⟩ := h T s
  let j : Over.mk (U.ι ≫ T.hom) ⟶ T := Over.homMk U.ι rfl
  have : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion U.ι)
  refine ⟨_, j, Over.mono_of_mono_left _, this, fun T' e => (hU T' e).trans ?_⟩
  refine Iff.trans ?_ (exists_comp_eq_iff_range_subset j e).symm
  change _ ↔ Set.range e.left ⊆ Set.range U.ι
  rw [Scheme.Opens.range_ι]

/-- **The open locus of an open subfunctor.** If the inclusion of a subfunctor `G` of a presheaf
`F` on the schemes over `S` is representable by open immersions, then for every section `s` of `F`
over `T` there is an open `U` of `T` such that the restriction of `s` along `g : T' ⟶ T` lies in
`G` exactly when `g` lands in `U`. -/
theorem exists_openLocus_of_isOpenImmersion_over_presheaf {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u} {G : Subfunctor F}
    (hG : (IsOpenImmersion.over (X := S)).presheaf G.ι) (T : Over S) (s : F.obj (op T)) :
    ∃ U : T.left.Opens, ∀ (T' : Over S) (g : T' ⟶ T),
      F.map g.op s ∈ G.obj (op T') ↔ Set.range g.left ⊆ U := by
  obtain ⟨V, j, hj, hV⟩ := exists_factor_of_presheaf_subfunctor_ι hG T s
  have : IsOpenImmersion j.left := hj
  exact ⟨j.left.opensRange, fun T' g =>
    (hV T' g).trans (exists_comp_eq_iff_range_subset j g)⟩

/-- **The total subfunctor of an open subfunctor is an open subfunctor.** If the inclusion of a
subfunctor `G` of a presheaf on the schemes over `S` is representable by open immersions, so is
the inclusion of its total subfunctor into the total presheaf on all schemes. -/
theorem isOpenImmersion_presheaf_totalSubfunctor_ι {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u} {G : Subfunctor F}
    (hG : (IsOpenImmersion.over (X := S)).presheaf G.ι) :
    IsOpenImmersion.presheaf (totalSubfunctor G).ι := by
  refine presheaf_subfunctor_ι_of_factor _ _ fun T x => ?_
  obtain ⟨a, s⟩ := x
  obtain ⟨U, j, hj, hU⟩ := exists_factor_of_presheaf_subfunctor_ι hG (Over.mk a) s
  have : IsOpenImmersion j.left := hj
  refine ⟨U.left, j.left, inferInstance, hj, fun T' e => ?_⟩
  change F.map (Over.homMk e rfl : Over.mk (e ≫ a) ⟶ Over.mk a).op s ∈ G.obj _ ↔ _
  rw [hU]
  constructor
  · rintro ⟨l, hl⟩
    exact ⟨l.left, by rw [← Over.comp_left, hl]; rfl⟩
  · rintro ⟨l, hl⟩
    have hw : l ≫ U.hom = e ≫ a := by
      rw [← Over.w j, ← Category.assoc, hl]
      rfl
    exact ⟨Over.homMk l hw, Over.OverMorphism.ext hl⟩

/-- **Local representability for presheaves on the schemes over `S`.** A Zariski sheaf of sets
on the schemes over `S` is representable as soon as it has a family of representable subfunctors
whose inclusions are representable by open immersions and which meet every point with values in
a field.

This is Mathlib's `AlgebraicGeometry.Scheme.LocalRepresentability.isRepresentable` applied to the
total presheaf `Stacks.Sites.totalPresheaf F` on all schemes. -/
theorem isRepresentable_of_isOpenImmersion_subfunctors {S : Scheme.{u}}
    (F : (Over S)ᵒᵖ ⥤ Type u) (hF : Presheaf.IsSheaf (Scheme.zariskiTopology.over S) F)
    {ι : Type u} (G : ι → Subfunctor F) (hrep : ∀ i, (G i).toFunctor.IsRepresentable)
    (hopen : ∀ i, (IsOpenImmersion.over (X := S)).presheaf (G i).ι)
    (hcover : ∀ (K : Type u) [Field K] (x : Spec (.of K) ⟶ S)
      (s : F.obj (op (Over.mk x))), ∃ i, s ∈ (G i).obj (op (Over.mk x))) :
    F.IsRepresentable := by
  have htot (i : ι) : IsOpenImmersion.presheaf (totalSubfunctor (G i)).ι :=
    isOpenImmersion_presheaf_totalSubfunctor_ι (hopen i)
  let Yr (i : ι) : Over S := (hrep i).has_representation.choose
  let R (i : ι) : (G i).toFunctor.RepresentableBy (Yr i) :=
    (hrep i).has_representation.choose_spec.some
  let e (i : ι) : yoneda.obj (Yr i).left ≅ (totalSubfunctor (G i)).toFunctor :=
    Functor.representableByEquiv (totalPresheafRepresentableBy (R i)) ≪≫
      (totalSubfunctorIso (G i)).symm
  let f (i : ι) : yoneda.obj (Yr i).left ⟶ totalPresheaf F := (e i).hom ≫ (totalSubfunctor (G i)).ι
  have hf (i : ι) : IsOpenImmersion.presheaf (f i) :=
    (MorphismProperty.cancel_left_of_respectsIso _ _ _).2 (htot i)
  let Ftot : Sheaf Scheme.zariskiTopology (Type u) :=
    ⟨totalPresheaf F, (isSheaf_iff_isSheaf_of_type _ _).2
      ((isSheaf_over_iff_isSheaf_totalPresheaf _ F
        (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)).1
        ((isSheaf_iff_isSheaf_of_type _ _).1 hF))⟩
  have : Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc f) := by
    refine ⟨fun {U} x => ?_⟩
    have hpt (p : U) : ∃ i, (totalPresheaf F).map (U.fromSpecResidueField p).op x ∈
        (totalSubfunctor (G i)).obj _ :=
      hcover (U.residueField p) _ _
    choose i hi using hpt
    choose W j hj hW using fun p => exists_factor_of_presheaf_subfunctor_ι (htot (i p)) U x
    have hcov (p : U) : ∃ q y, j q y = p := by
      obtain ⟨l, hl⟩ := (hW p _ _).1 (hi p)
      obtain ⟨z, hz⟩ : p ∈ Set.range (U.fromSpecResidueField p) := by
        rw [Scheme.range_fromSpecResidueField]
        simp
      exact ⟨p, l z, by rw [← Scheme.Hom.comp_apply, hl, hz]⟩
    let 𝒰 : U.OpenCover := Scheme.Cover.mkOfCovers U W j hcov hj
    refine Scheme.zariskiTopology.superset_covering ?_ 𝒰.mem_grothendieckTopology
    rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro _ _ ⟨p⟩
    have hmem := (hW p (W p) (j p)).2 ⟨𝟙 _, Category.id_comp _⟩
    refine ⟨(Sigma.ι (fun i => yoneda.obj (Yr i).left) (i p)).app _
      ((e (i p)).inv.app _ ⟨_, hmem⟩), ?_⟩
    have hc := congrArg (fun n => n.app (op (W p)) ((e (i p)).inv.app _ ⟨_, hmem⟩))
      (Sigma.ι_comp_desc f (i p))
    exact hc.trans (congrArg (fun z => (totalSubfunctor (G (i p))).ι.app (op (W p)) z)
      (ConcreteCategory.congr_hom ((e (i p)).inv_hom_id_app (op (W p))) _))
  exact isRepresentable_of_isRepresentable_totalPresheaf
    (Scheme.LocalRepresentability.isRepresentable (F := Ftot) (f := f) hf)

end AlgebraicGeometry
