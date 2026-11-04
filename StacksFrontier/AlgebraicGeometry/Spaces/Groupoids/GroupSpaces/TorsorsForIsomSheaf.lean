module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.CategoryOfFppfTorsors
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Stack

/-!
# The `Isom` presheaves of a category of torsors of algebraic spaces are sheaves

Let `B` be an algebraic space over a scheme `S` of a big fppf site, let `G` be a group algebraic
space over `B` and let `P` be any property of families of morphisms to a presheaf.  The torsors
under `G` trivialized by a family satisfying `P` form a category
`AlgebraicGeometry.Space.TorsorsFor hB G P` over the big fppf site of `S`, which is the category
`G-Torsors` of Stacks 04UR for the fppf coverings and the category `G-Principal` of Stacks 04UN for
the fpqc coverings.  This file proves condition (2) of Stacks 02ZI for its projection to the site,
for every `P`: for two objects over the same object `U` of the site, a family of isomorphisms of
their restrictions along a covering family of `U` which agree on the overlaps glues, uniquely, to
an isomorphism over `U`.

The argument does not see `P` at all.  The total spaces are algebraic spaces, hence sheaves, and
the total space of a restriction along `f : V ⟶ U` is the base change of the total space along
`f`.  So the total spaces of the restrictions along a covering family jointly lift every section
of the total space locally, and a map out of a presheaf into a sheaf prescribed compatibly on
such a family exists and is unique.  The glued map is cartesian over the identity of `U` and
equivariant because both properties may be tested on the same family, and the two sections of
`B` agree because `B` is a sheaf.

## Main definitions

* `CategoryTheory.Presheaf.liftingSieve`: the sieve along which a section of a presheaf lifts to a
  member of a family of presheaves mapping to it.
* `CategoryTheory.Presheaf.IsJointlyLocallySurjective`: every section lifts in this way locally.

## Main results

* `CategoryTheory.Presheaf.IsJointlyLocallySurjective.hom_ext` and
  `CategoryTheory.Presheaf.IsJointlyLocallySurjective.existsUnique_hom`: maps from the target of a
  jointly locally surjective family into a sheaf are determined by, and glue from, compatible
  maps on the members.
* `CategoryTheory.Presheaf.isJointlyLocallySurjective_of_isPullback`: the base changes of a
  presheaf over `U` along a covering family of `U` are jointly locally surjective.
* `AlgebraicGeometry.Space.TorsorsFor.projection_isomIsSheaf`: condition (2) of Stacks 02ZI for
  `p : TorsorsFor hB G P ⥤ (Sch/S)_fppf`, for every covering property `P`.

## Implementation notes

No tag is carried.  For the fppf coverings the statement is condition (2) of Stacks 04US, which
the library registers on `AlgebraicGeometry.Space.FppfTorsors.projection_isomIsSheaf`; for the
fpqc coverings it is the second of the three conditions in the conjecture of Stacks 04UP and is
consumed by `AlgebraicGeometry.Space.PrincipalHomogeneousSpaces.isStackInGroupoids_of_descent`.

## References

* [Stacks Project, Tag 02ZI](https://stacks.math.columbia.edu/tag/02ZI)
* [Stacks Project, Tag 04UN](https://stacks.math.columbia.edu/tag/04UN)
* [Stacks Project, Tag 04UR](https://stacks.math.columbia.edu/tag/04UR)
* [Stacks Project, Tag 04UP](https://stacks.math.columbia.edu/tag/04UP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory MonObj

universe w u u₁ v₁ u₂ w₁

namespace CategoryTheory.Presheaf

variable {C : Type u₁} [Category.{v₁} C]

/-- The sieve on `W` of the arrows `g : Z ⟶ W` along which a section `x` of `P` over `W` becomes
the image of a section of one of the presheaves `F i` under `π i : F i ⟶ P`. -/
def liftingSieve {P : Cᵒᵖ ⥤ Type u₂} {I : Type w₁} {F : I → Cᵒᵖ ⥤ Type u₂}
    (π : ∀ i, F i ⟶ P) {W : C} (x : P.obj (Opposite.op W)) : Sieve W where
  arrows {Z} g := ∃ (i : I) (t : (F i).obj (Opposite.op Z)), (π i).app _ t = P.map g.op x
  downward_closed := by
    rintro Z Y g ⟨i, t, ht⟩ k
    refine ⟨i, (F i).map k.op t, ?_⟩
    rw [(π i).naturality_apply, ht]
    simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

/-- A family of maps of presheaves `π i : F i ⟶ P` is *jointly locally surjective* for `J` when
every section of `P` lifts, locally for `J`, to a section of one of the `F i`. -/
def IsJointlyLocallySurjective (J : GrothendieckTopology C) {P : Cᵒᵖ ⥤ Type u₂} {I : Type w₁}
    {F : I → Cᵒᵖ ⥤ Type u₂} (π : ∀ i, F i ⟶ P) : Prop :=
  ∀ (W : C) (x : P.obj (Opposite.op W)), liftingSieve π x ∈ J W

namespace IsJointlyLocallySurjective

variable {J : GrothendieckTopology C} {P Q : Cᵒᵖ ⥤ Type u₂} {I : Type w₁}
  {F : I → Cᵒᵖ ⥤ Type u₂} {π : ∀ i, F i ⟶ P}

/-- Two maps from the target of a jointly locally surjective family into a sheaf which agree on
every member of the family are equal. -/
theorem hom_ext (hπ : IsJointlyLocallySurjective J π) (hQ : Presheaf.IsSheaf J Q)
    {g g' : P ⟶ Q} (h : ∀ i, π i ≫ g = π i ≫ g') : g = g' := by
  ext W x
  apply (hQ.isSheafFor _ (hπ W.unop x)).isSeparatedFor.ext
  rintro Z k ⟨i, t, ht⟩
  calc
    _ = g.app _ (P.map k.op x) := (g.naturality_apply k.op x).symm
    _ = g'.app _ (P.map k.op x) := by
      rw [← ht]
      exact congrArg (fun m : F i ⟶ Q => m.app _ t) (h i)
    _ = _ := g'.naturality_apply k.op x

/-- Maps from the members of a jointly locally surjective family into a sheaf which agree on any
two sections with the same image glue, uniquely, to a map from the target. -/
theorem existsUnique_hom (hπ : IsJointlyLocallySurjective J π) (hQ : Presheaf.IsSheaf J Q)
    (τ : ∀ i, F i ⟶ Q)
    (hτ : ∀ (W : C) (i j : I) (s : (F i).obj (Opposite.op W))
      (t : (F j).obj (Opposite.op W)), (π i).app _ s = (π j).app _ t →
        (τ i).app _ s = (τ j).app _ t) :
    ∃! g : P ⟶ Q, ∀ i, π i ≫ g = τ i := by
  classical
  let a {W : C} (x : P.obj (Opposite.op W)) :
      Presieve.FamilyOfElements Q (liftingSieve π x).arrows :=
    fun Z f hf => (τ hf.choose).app _ hf.choose_spec.choose
  have ha {W Z : C} (x : P.obj (Opposite.op W)) (f : Z ⟶ W)
      (hf : liftingSieve π x f) (i : I) (t : (F i).obj (Opposite.op Z))
      (ht : (π i).app _ t = P.map f.op x) : a x f hf = (τ i).app _ t :=
    hτ Z _ i _ t (hf.choose_spec.choose_spec.trans ht.symm)
  have ac {W : C} (x : P.obj (Opposite.op W)) : (a x).Compatible := by
    intro Z₁ Z₂ Z g₁ g₂ f₁ f₂ h₁ h₂ hw
    dsimp only [a]
    rw [← (τ h₁.choose).naturality_apply, ← (τ h₂.choose).naturality_apply]
    apply hτ
    rw [(π h₁.choose).naturality_apply, (π h₂.choose).naturality_apply,
      h₁.choose_spec.choose_spec, h₂.choose_spec.choose_spec]
    simp only [← ConcreteCategory.comp_apply, ← CategoryTheory.Functor.map_comp, ← op_comp, hw]
  let g {W : C} (x : P.obj (Opposite.op W)) :=
    (hQ.isSheafFor _ (hπ W x)).amalgamate (a x) (ac x)
  have hg {W Z : C} (x : P.obj (Opposite.op W)) (f : Z ⟶ W)
      (hf : liftingSieve π x f) (i : I) (t : (F i).obj (Opposite.op Z))
      (ht : (π i).app _ t = P.map f.op x) :
      Q.map f.op (g x) = (τ i).app _ t :=
    ((hQ.isSheafFor _ (hπ W x)).isAmalgamation (ac x) f hf).trans (ha x f hf i t ht)
  have gn {W Z : C} (f : Z ⟶ W) (x : P.obj (Opposite.op W)) :
      Q.map f.op (g x) = g (P.map f.op x) := by
    apply (hQ.isSheafFor _ (hπ Z (P.map f.op x))).isSeparatedFor.ext
    rintro Y k ⟨i, t, ht⟩
    have ht' : (π i).app _ t = P.map (k ≫ f).op x := by
      simpa only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply] using ht
    rw [← ConcreteCategory.comp_apply, ← Q.map_comp, ← op_comp]
    exact (hg x (k ≫ f) ⟨i, t, ht'⟩ i t ht').trans
      (hg (P.map f.op x) k ⟨i, t, ht⟩ i t ht).symm
  let θ : P ⟶ Q :=
    { app := fun W => ↾(fun x => g x)
      naturality := by
        intro W Z f
        ext x
        exact (gn f.unop x).symm }
  have hθ (i : I) : π i ≫ θ = τ i := by
    ext W t
    simpa [θ] using hg ((π i).app W t) (𝟙 W.unop)
      (show liftingSieve π ((π i).app W t) (𝟙 W.unop) from ⟨i, t, by simp⟩) i t (by simp)
  exact ⟨θ, hθ, fun θ' hθ' => hπ.hom_ext hQ (fun i => (hθ' i).trans (hθ i).symm)⟩

/-- Precomposing the members of a jointly locally surjective family with isomorphisms gives a
jointly locally surjective family. -/
theorem iso_comp (hπ : IsJointlyLocallySurjective J π) {F' : I → Cᵒᵖ ⥤ Type u₂}
    (e : ∀ i, F' i ≅ F i) : IsJointlyLocallySurjective J (fun i => (e i).hom ≫ π i) := by
  intro W x
  refine J.superset_covering ?_ (hπ W x)
  rintro Z k ⟨i, t, ht⟩
  refine ⟨i, (e i).inv.app _ t, ?_⟩
  show (π i).app _ ((e i).hom.app _ ((e i).inv.app _ t)) = _
  simpa using ht

/-- Two sheaves receiving jointly locally surjective families from the same presheaves, which
cut out the same relation between the sections of any two members, are isomorphic compatibly
with the two families. -/
theorem exists_iso (hπ : IsJointlyLocallySurjective J π) (hP : Presheaf.IsSheaf J P)
    (hQ : Presheaf.IsSheaf J Q) {τ : ∀ i, F i ⟶ Q} (hτ : IsJointlyLocallySurjective J τ)
    (hrel : ∀ (W : C) (i j : I) (s : (F i).obj (Opposite.op W))
      (t : (F j).obj (Opposite.op W)), (π i).app _ s = (π j).app _ t ↔
        (τ i).app _ s = (τ j).app _ t) :
    ∃ e : P ≅ Q, ∀ i, π i ≫ e.hom = τ i := by
  obtain ⟨g, hg, -⟩ := hπ.existsUnique_hom hQ τ (fun W i j s t => (hrel W i j s t).1)
  obtain ⟨g', hg', -⟩ := hτ.existsUnique_hom hP π (fun W i j s t => (hrel W i j s t).2)
  refine ⟨⟨g, g', ?_, ?_⟩, hg⟩
  · refine hπ.hom_ext hP fun i => ?_
    rw [← Category.assoc, hg, hg', Category.comp_id]
  · refine hτ.hom_ext hQ fun i => ?_
    rw [← Category.assoc, hg', hg, Category.comp_id]

end IsJointlyLocallySurjective

/-- The base changes of a presheaf over `U` along a covering family of `U` are jointly locally
surjective. -/
theorem isJointlyLocallySurjective_of_isPullback (J : GrothendieckTopology C)
    {U : C} {P : Cᵒᵖ ⥤ Type v₁} (q : P ⟶ yoneda.obj U)
    {I : Type w₁} {V : I → C} (f : ∀ i, V i ⟶ U) (hf : Sieve.ofArrows V f ∈ J U)
    {F : I → Cᵒᵖ ⥤ Type v₁} (π : ∀ i, F i ⟶ P) (q' : ∀ i, F i ⟶ yoneda.obj (V i))
    (h : ∀ i, IsPullback (π i) (q' i) q (yoneda.map (f i))) :
    IsJointlyLocallySurjective J π := by
  intro W x
  apply J.superset_covering _ (J.pullback_stable (q.app _ x) hf)
  rintro Z g ⟨Y, k, l, ⟨i⟩, he⟩
  have hw : q.app _ (P.map g.op x) = (yoneda.map (f i)).app _ k :=
    (q.naturality_apply g.op x).trans he.symm
  obtain ⟨t, ht, -⟩ := Types.exists_of_isPullback
    ((h i).map ((evaluation _ _).obj (Opposite.op Z))) (P.map g.op x) k hw
  exact ⟨i, t, ht⟩

/-- A family of base changes of a fibre product of presheaves is jointly locally surjective as
soon as the family of base changes of its second factor is. -/
theorem IsJointlyLocallySurjective.pullback_map {J : GrothendieckTopology C}
    {A P R : Cᵒᵖ ⥤ Type u₂} (a : A ⟶ R) (p : P ⟶ R)
    {I : Type w₁} {A' P' R' : I → Cᵒᵖ ⥤ Type u₂}
    (a' : ∀ i, A' i ⟶ R' i) (p' : ∀ i, P' i ⟶ R' i)
    (α : ∀ i, A' i ⟶ A) (π : ∀ i, P' i ⟶ P) (ρ : ∀ i, R' i ⟶ R)
    (hA : ∀ i, IsPullback (α i) (a' i) a (ρ i))
    (hP : ∀ i, IsPullback (π i) (p' i) p (ρ i))
    (hπ : IsJointlyLocallySurjective J π) :
    IsJointlyLocallySurjective J (fun i => pullback.map (a' i) (p' i) a p (α i) (π i) (ρ i)
      (hA i).w.symm (hP i).w.symm) := by
  intro W x
  apply J.superset_covering _ (hπ W ((pullback.snd a p).app _ x))
  rintro Z f ⟨i, t, ht⟩
  let E := (evaluation Cᵒᵖ (Type u₂)).obj (Opposite.op Z)
  let z := (pullback a p).map f.op x
  have hz : (pullback.snd a p).app _ z = (π i).app _ t :=
    ((pullback.snd a p).naturality_apply f.op x).trans ht.symm
  have hw : a.app _ ((pullback.fst a p).app _ z) = (ρ i).app _ ((p' i).app _ t) := by
    calc
      _ = p.app _ ((pullback.snd a p).app _ z) :=
        congrArg (fun k : pullback a p ⟶ R => k.app _ z) pullback.condition
      _ = p.app _ ((π i).app _ t) := congrArg (p.app _) hz
      _ = _ := congrArg (fun k : P' i ⟶ R => k.app _ t) (hP i).w
  obtain ⟨s, hs, hs'⟩ := Types.exists_of_isPullback ((hA i).map E)
    ((pullback.fst a p).app _ z) ((p' i).app _ t) hw
  obtain ⟨v, hv, hv'⟩ := Types.exists_of_isPullback
    ((IsPullback.of_hasPullback (a' i) (p' i)).map E) s t hs'
  change (α i).app (Opposite.op Z) s = (pullback.fst a p).app _ z at hs
  change (pullback.fst (a' i) (p' i)).app (Opposite.op Z) v = s at hv
  change (pullback.snd (a' i) (p' i)).app (Opposite.op Z) v = t at hv'
  refine ⟨i, v, ?_⟩
  apply Types.ext_of_isPullback ((IsPullback.of_hasPullback a p).map E)
  · have hmap : pullback.map (a' i) (p' i) a p (α i) (π i) (ρ i)
        (hA i).w.symm (hP i).w.symm ≫ pullback.fst a p =
        pullback.fst (a' i) (p' i) ≫ α i := pullback.lift_fst _ _ _
    exact (congrArg (fun k => k.app (Opposite.op Z) v) hmap).trans
      (by simpa only [NatTrans.comp_app, ConcreteCategory.comp_apply, hv] using hs)
  · have hmap : pullback.map (a' i) (p' i) a p (α i) (π i) (ρ i)
        (hA i).w.symm (hP i).w.symm ≫ pullback.snd a p =
        pullback.snd (a' i) (p' i) ≫ π i := pullback.lift_snd _ _ _
    exact (congrArg (fun k => k.app (Opposite.op Z) v) hmap).trans
      (by simpa only [NatTrans.comp_app, ConcreteCategory.comp_apply, hv'] using hz.symm)

end CategoryTheory.Presheaf

namespace AlgebraicGeometry.Space

open CategoryTheory.Presheaf

variable {𝒞 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝒞.Contains S}
  {B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u} {hB : IsAlgebraicSpace 𝒞 S hS B}
  {G : GroupAlgebraicSpace 𝒞 S hS B hB} {P : CoveringPredicate 𝒞 S hS}

namespace TorsorsFor

/-- The action morphism of a torsor, as a map of presheaves. -/
abbrev actionMap (T : TorsorsFor hB G P) :
    pullback (pullback.snd G.obj.X.hom T.sec) T.total.hom ⟶ T.total.left :=
  (γ[T.group, T.total]).left

/-- The structure morphism of the total space of a torsor, read as a map to a prescribed object
of the site equal to its base. -/
abbrev normalizedProjection (T : TorsorsFor hB G P) {U : BigFppfOver 𝒞 S hS}
    (hT : T.base = U) : T.total.left ⟶ yoneda.obj U :=
  T.total.hom ≫ yoneda.map (eqToHom hT)

/-- The section of `B` carried by a torsor, read over a prescribed object of the site equal to
its base. -/
abbrev normalizedSection (T : TorsorsFor hB G P) {U : BigFppfOver 𝒞 S hS}
    (hT : T.base = U) : yoneda.obj U ⟶ B :=
  yoneda.map (eqToHom hT.symm) ≫ T.sec

/-- A morphism of torsors lying over a morphism of the site has that morphism as its morphism of
bases. -/
theorem base_eq_of_isHomLift {T T' : TorsorsFor hB G P} (φ : T ⟶ T') (f : T.base ⟶ T'.base)
    (h : (projection hB G P).IsHomLift f φ) : Hom.base φ = f :=
  (@CategoryTheory.IsHomLift.eq_of_isHomLift _ _ _ _ (projection hB G P) T T' f φ h).symm

/-- The morphism of total spaces of a morphism of torsors identifies the source total space with
the base change of the target one, read over prescribed bases. -/
theorem isPullback_normalizedProjection {T T' : TorsorsFor hB G P}
    {V U : BigFppfOver 𝒞 S hS} (hT : T.base = V) (hT' : T'.base = U)
    (φ : T ⟶ T') (f : V ⟶ U) (hf : Hom.base φ = eqToHom hT ≫ f ≫ eqToHom hT'.symm) :
    IsPullback (Hom.map φ) (normalizedProjection T hT) (normalizedProjection T' hT')
      (yoneda.map f) := by
  subst V
  subst U
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hf
  simpa [normalizedProjection, hf] using Hom.isPullback φ

/-- A morphism of torsors is compatible with the sections of `B`, read over prescribed bases. -/
theorem comp_normalizedSection {T T' : TorsorsFor hB G P}
    {V U : BigFppfOver 𝒞 S hS} (hT : T.base = V) (hT' : T'.base = U)
    (φ : T ⟶ T') (f : V ⟶ U) (hf : Hom.base φ = eqToHom hT ≫ f ≫ eqToHom hT'.symm) :
    yoneda.map f ≫ normalizedSection T' hT' = normalizedSection T hT := by
  subst V
  subst U
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hf
  simpa [normalizedSection, hf] using Hom.comp_sec φ

/-- The total space of a restriction of a torsor along a morphism of the site is the base change
of the total space. -/
theorem Restriction.isPullback {U V : BigFppfOver 𝒞 S hS} (T : TorsorsFor hB G P)
    (hT : T.base = U) (f : V ⟶ U) (r : Functor.Restriction (projection hB G P) f T hT) :
    IsPullback (Hom.map r.hom) (normalizedProjection r.pt r.hpt)
      (normalizedProjection T hT) (yoneda.map f) :=
  isPullback_normalizedProjection r.hpt hT r.hom f (base_eq_of_isHomLift r.hom _ r.isHomLift)

/-- The comparison morphism between two restrictions of a torsor lies over the morphism of the
site relating them. -/
theorem Restriction.compTo_base {U V W : BigFppfOver 𝒞 S hS} (T : TorsorsFor hB G P)
    (hT : T.base = U) (f : V ⟶ U) (k : W ⟶ V) {l : W ⟶ U} (hl : l = k ≫ f)
    (r : Functor.Restriction (projection hB G P) f T hT)
    (s : Functor.Restriction (projection hB G P) l T hT) :
    Hom.base (Functor.Restriction.compTo (projection hB G P) k f hl r s) =
      eqToHom s.hpt ≫ k ≫ eqToHom r.hpt.symm := by
  have hlift : (projection hB G P).IsHomLift (eqToHom s.hpt ≫ k ≫ eqToHom r.hpt.symm)
      (Functor.Restriction.compTo (projection hB G P) k f hl r s) := by
    unfold Functor.Restriction.compTo
    infer_instance
  exact base_eq_of_isHomLift _ _ hlift

/-- The two comparison morphisms from a restriction over an overlap of a covering family to the
restrictions over the two members exhibit it as their fibre product. -/
theorem Restriction.overlap_isPullback {U V₁ V₂ W : BigFppfOver 𝒞 S hS}
    (T : TorsorsFor hB G P) (hT : T.base = U) (f₁ : V₁ ⟶ U) (f₂ : V₂ ⟶ U)
    (p₁ : W ⟶ V₁) (p₂ : W ⟶ V₂) (hp : IsPullback p₁ p₂ f₁ f₂)
    (r₁ : Functor.Restriction (projection hB G P) f₁ T hT)
    (r₂ : Functor.Restriction (projection hB G P) f₂ T hT)
    (s : Functor.Restriction (projection hB G P) (p₁ ≫ f₁) T hT) :
    IsPullback
      (Hom.map (Functor.Restriction.compTo (projection hB G P) p₁ f₁ rfl r₁ s))
      (Hom.map (Functor.Restriction.compTo (projection hB G P) p₂ f₂ hp.w r₂ s))
      (Hom.map r₁.hom) (Hom.map r₂.hom) := by
  let c₁ := Functor.Restriction.compTo (projection hB G P) p₁ f₁ rfl r₁ s
  let c₂ := Functor.Restriction.compTo (projection hB G P) p₂ f₂ hp.w r₂ s
  have hc₁ := isPullback_normalizedProjection s.hpt r₁.hpt c₁ p₁
    (Restriction.compTo_base T hT f₁ p₁ rfl r₁ s)
  have hc₂ := isPullback_normalizedProjection s.hpt r₂.hpt c₂ p₂
    (Restriction.compTo_base T hT f₂ p₂ hp.w r₂ s)
  have e₁ : Hom.map c₁ ≫ Hom.map r₁.hom = Hom.map s.hom :=
    congrArg Hom.map (Functor.Restriction.compTo_hom (projection hB G P) p₁ f₁ rfl r₁ s)
  have e₂ : Hom.map c₂ ≫ Hom.map r₂.hom = Hom.map s.hom :=
    congrArg Hom.map (Functor.Restriction.compTo_hom (projection hB G P) p₂ f₂ hp.w r₂ s)
  have outer := hc₁.paste_vert (hp.map yoneda)
  rw [← hc₂.w, ← (Restriction.isPullback T hT f₁ r₁).w] at outer
  exact IsPullback.of_bot outer (e₁.trans e₂.symm) (Restriction.isPullback T hT f₂ r₂)

/-- The total spaces of the restrictions of a torsor along a covering family are jointly locally
surjective onto its total space. -/
theorem Restriction.isJointlyLocallySurjective {U : BigFppfOver 𝒞 S hS}
    (T : TorsorsFor hB G P) (hT : T.base = U)
    {I : Type w} (V : I → BigFppfOver 𝒞 S hS) (f : ∀ i, V i ⟶ U)
    (hf : Sieve.ofArrows V f ∈ BigFppfOver.topology 𝒞 S hS U)
    (r : ∀ i, Functor.Restriction (projection hB G P) (f i) T hT) :
    IsJointlyLocallySurjective (BigFppfOver.topology 𝒞 S hS) (fun i => Hom.map (r i).hom) :=
  isJointlyLocallySurjective_of_isPullback _ (normalizedProjection T hT) f hf
    (fun i => Hom.map (r i).hom) (fun i => normalizedProjection (r i).pt (r i).hpt)
    (fun i => Restriction.isPullback T hT (f i) (r i))

/-- Base change of the acting group along a morphism of torsors exhibits the acting group of the
source as the fibre product of that of the target with the source base. -/
theorem isPullback_groupBaseChange {T T' : TorsorsFor hB G P} (φ : T ⟶ T') :
    IsPullback (groupBaseChange (Hom.base φ) (Hom.comp_sec φ)) T.group.hom T'.group.hom
      (yoneda.map (Hom.base φ)) := by
  apply IsPullback.of_right (h₁₂ := pullback.fst G.obj.X.hom T'.sec) (h₂₂ := T'.sec)
    _ (groupBaseChange_snd _ _) (IsPullback.of_hasPullback _ _)
  simpa only [groupBaseChange_fst, Hom.comp_sec φ] using
    IsPullback.of_hasPullback G.obj.X.hom T.sec

/-- The base changes of the action to the restrictions of a torsor along a covering family are
jointly locally surjective onto the fibre product on which the acting group acts. -/
theorem Restriction.isJointlyLocallySurjective_action {U : BigFppfOver 𝒞 S hS}
    (T : TorsorsFor hB G P) (hT : T.base = U)
    {I : Type w} (V : I → BigFppfOver 𝒞 S hS) (f : ∀ i, V i ⟶ U)
    (hf : Sieve.ofArrows V f ∈ BigFppfOver.topology 𝒞 S hS U)
    (r : ∀ i, Functor.Restriction (projection hB G P) (f i) T hT) :
    IsJointlyLocallySurjective (BigFppfOver.topology 𝒞 S hS)
      (fun i => actionBaseChange (Hom.base (r i).hom) (Hom.comp_sec (r i).hom)
        (Hom.map (r i).hom) (Hom.isPullback (r i).hom).w.symm) :=
  IsJointlyLocallySurjective.pullback_map T.group.hom T.total.hom
    (fun i => (r i).pt.group.hom) (fun i => (r i).pt.total.hom)
    (fun i => groupBaseChange (Hom.base (r i).hom) (Hom.comp_sec (r i).hom))
    (fun i => Hom.map (r i).hom) (fun i => yoneda.map (Hom.base (r i).hom))
    (fun i => isPullback_groupBaseChange (r i).hom) (fun i => Hom.isPullback (r i).hom)
    (Restriction.isJointlyLocallySurjective T hT V f hf r)

/-- Base change of the action depends only on the two underlying morphisms. -/
theorem actionBaseChange_congr {T T' : TorsorsFor hB G P}
    {f f' : T.base ⟶ T'.base} {hf : yoneda.map f ≫ T'.sec = T.sec}
    {hf' : yoneda.map f' ≫ T'.sec = T.sec} {g g' : T.total.left ⟶ T'.total.left}
    {hg : T.total.hom ≫ yoneda.map f = g ≫ T'.total.hom}
    {hg' : T.total.hom ≫ yoneda.map f' = g' ≫ T'.total.hom}
    (hff : f = f') (hgg : g = g') :
    actionBaseChange f hf g hg = actionBaseChange f' hf' g' hg' := by
  subst f'
  subst g'
  rfl

/-- A morphism of torsors lying over an identity of the base has an isomorphism of total spaces. -/
private theorem isIso_map_of_fibreHom {x y : TorsorsFor hB G P} {V : BigFppfOver 𝒞 S hS}
    (hx : x.base = V) (hy : y.base = V) (φ : x ⟶ y)
    (hφ : Functor.FibreHom (projection hB G P) x y hx hy φ) : IsIso (Hom.map φ) := by
  have hb : Hom.base φ = eqToHom hx ≫ eqToHom hy.symm := base_eq_of_isHomLift φ _ hφ
  have : IsIso (Hom.base φ) := by
    rw [hb, eqToHom_trans]
    infer_instance
  exact (Hom.isPullback φ).isIso_fst_of_isIso

/-- A family of isomorphisms between the restrictions of two torsors along a covering family
which agree on the overlaps glues to an isomorphism of their total spaces. -/
theorem Restriction.exists_glued_iso {U : BigFppfOver 𝒞 S hS} (x y : TorsorsFor hB G P)
    (hx : (projection hB G P).obj x = U) (hy : (projection hB G P).obj y = U)
    {I : Type w} (V : I → BigFppfOver 𝒞 S hS) (f : ∀ i, V i ⟶ U)
    (hf : Sieve.ofArrows V f ∈ BigFppfOver.topology 𝒞 S hS U)
    (Vij : I → I → BigFppfOver 𝒞 S hS)
    (pr₁ : ∀ i j, Vij i j ⟶ V i) (pr₂ : ∀ i j, Vij i j ⟶ V j)
    (hVij : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j))
    (xr : ∀ i, Functor.Restriction (projection hB G P) (f i) x hx)
    (yr : ∀ i, Functor.Restriction (projection hB G P) (f i) y hy)
    (xrij : ∀ i j, Functor.Restriction (projection hB G P) (pr₁ i j ≫ f i) x hx)
    (yrij : ∀ i j, Functor.Restriction (projection hB G P) (pr₁ i j ≫ f i) y hy)
    (φ : ∀ i, (xr i).pt ⟶ (yr i).pt)
    (hφ : ∀ i, Functor.FibreHom (projection hB G P) (xr i).pt (yr i).pt
      (xr i).hpt (yr i).hpt (φ i))
    (hc : ∀ i j, ∃ (θ : (xrij i j).pt ⟶ (yrij i j).pt),
      Functor.FibreHom (projection hB G P) (xrij i j).pt (yrij i j).pt
        (xrij i j).hpt (yrij i j).hpt θ ∧
      Functor.IsRestrictionOf (projection hB G P) (pr₁ i j) rfl rfl
        (xr i) (yr i) (xrij i j) (yrij i j) (φ i) θ ∧
      Functor.IsRestrictionOf (projection hB G P) (pr₂ i j) (hVij i j).w (hVij i j).w
        (xr j) (yr j) (xrij i j) (yrij i j) (φ j) θ) :
    ∃ e : x.total.left ≅ y.total.left,
      ∀ i, Hom.map (xr i).hom ≫ e.hom = Hom.map (φ i) ≫ Hom.map (yr i).hom := by
  have hi (i : I) : IsIso (Hom.map (φ i)) :=
    isIso_map_of_fibreHom (xr i).hpt (yr i).hpt (φ i) (hφ i)
  have := hi
  refine IsJointlyLocallySurjective.exists_iso
    (Restriction.isJointlyLocallySurjective x hx V f hf xr) x.isAlgebraicSpace.isSheaf
    y.isAlgebraicSpace.isSheaf ?_ ?_
  · exact (Restriction.isJointlyLocallySurjective y hy V f hf yr).iso_comp
      (fun i => asIso (Hom.map (φ i)))
  · intro W i j s t
    obtain ⟨θ, hθ, hθ₁, hθ₂⟩ := hc i j
    have : IsIso (Hom.map θ) := isIso_map_of_fibreHom (xrij i j).hpt (yrij i j).hpt θ hθ
    have px := Restriction.overlap_isPullback x hx (f i) (f j) (pr₁ i j) (pr₂ i j)
      (hVij i j) (xr i) (xr j) (xrij i j)
    have py := Restriction.overlap_isPullback y hy (f i) (f j) (pr₁ i j) (pr₂ i j)
      (hVij i j) (yr i) (yr j) (yrij i j)
    have py' : IsPullback
        (Hom.map (Functor.Restriction.compTo (projection hB G P) (pr₁ i j) (f i) rfl
          (xr i) (xrij i j)))
        (Hom.map (Functor.Restriction.compTo (projection hB G P) (pr₂ i j) (f j) (hVij i j).w
          (xr j) (xrij i j)))
        (Hom.map (φ i) ≫ Hom.map (yr i).hom) (Hom.map (φ j) ≫ Hom.map (yr j).hom) :=
      py.of_iso' (asIso (Hom.map θ)) (asIso (Hom.map (φ i))) (asIso (Hom.map (φ j)))
        (Iso.refl y.total.left) (congrArg Hom.map hθ₁) (congrArg Hom.map hθ₂)
        (by simp) (by simp)
    have hx' := px.map ((evaluation _ _).obj (Opposite.op W))
    have hy' := py'.map ((evaluation _ _).obj (Opposite.op W))
    constructor
    · intro e
      obtain ⟨z, rfl, rfl⟩ := Types.exists_of_isPullback hx' s t e
      exact congrArg (fun k => k z) hy'.w
    · intro e
      obtain ⟨z, rfl, rfl⟩ := Types.exists_of_isPullback hy' s t e
      exact congrArg (fun k => k z) hx'.w

/-- An isomorphism of the total spaces of two torsors over the same base, compatible with a
family of isomorphisms of their restrictions along a covering family, is a morphism of torsors.
The two sections of `B` agree because `B` is a sheaf. -/
theorem Restriction.exists_glued_hom {U : BigFppfOver 𝒞 S hS} (x y : TorsorsFor hB G P)
    (hx : (projection hB G P).obj x = U) (hy : (projection hB G P).obj y = U)
    (hxy : x.base = y.base)
    {I : Type w} (V : I → BigFppfOver 𝒞 S hS) (f : ∀ i, V i ⟶ U)
    (hf : Sieve.ofArrows V f ∈ BigFppfOver.topology 𝒞 S hS U)
    (xr : ∀ i, Functor.Restriction (projection hB G P) (f i) x hx)
    (yr : ∀ i, Functor.Restriction (projection hB G P) (f i) y hy)
    (φ : ∀ i, (xr i).pt ⟶ (yr i).pt)
    (hφ : ∀ i, Functor.FibreHom (projection hB G P) (xr i).pt (yr i).pt
      (xr i).hpt (yr i).hpt (φ i))
    (e : x.total.left ≅ y.total.left)
    (he : ∀ i, Hom.map (xr i).hom ≫ e.hom = Hom.map (φ i) ≫ Hom.map (yr i).hom) :
    ∃ g : x ⟶ y, Hom.base g = eqToHom hxy ∧ Hom.map g = e.hom ∧
      ∀ i, (xr i).hom ≫ g = φ i ≫ (yr i).hom := by
  have hx' : x.base = U := hx
  have hy' : y.base = U := hy
  have hxb (i : I) : (xr i).pt.base = V i := (xr i).hpt
  have hyb (i : I) : (yr i).pt.base = V i := (yr i).hpt
  have hφf (i : I) : Hom.base (φ i) = eqToHom (hxb i) ≫ eqToHom (hyb i).symm :=
    base_eq_of_isHomLift (φ i) _ (hφ i)
  have hφf' (i : I) : Hom.base (φ i) =
      eqToHom (hxb i) ≫ 𝟙 (V i) ≫ eqToHom (hyb i).symm := by rw [Category.id_comp, hφf i]
  have hxf (i : I) : Hom.base (xr i).hom = eqToHom (hxb i) ≫ f i ≫ eqToHom hx'.symm :=
    base_eq_of_isHomLift (xr i).hom _ (xr i).isHomLift
  have hyf (i : I) : Hom.base (yr i).hom = eqToHom (hyb i) ≫ f i ≫ eqToHom hy'.symm :=
    base_eq_of_isHomLift (yr i).hom _ (yr i).isHomLift
  have hfac (i : I) : Hom.base (xr i).hom ≫ eqToHom hxy =
      Hom.base (φ i) ≫ Hom.base (yr i).hom := by
    rw [hxf i, hyf i, hφf i]
    simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
  have hU : IsJointlyLocallySurjective (BigFppfOver.topology 𝒞 S hS)
      (fun i => yoneda.map (f i)) :=
    isJointlyLocallySurjective_of_isPullback _ (𝟙 (yoneda.obj U)) f hf
      (fun i => yoneda.map (f i)) (fun i => 𝟙 (yoneda.obj (V i)))
      (fun i => IsPullback.id_vert _)
  have hb' : normalizedSection x hx' = normalizedSection y hy' := by
    refine hU.hom_ext hB.isSheaf fun i => ?_
    rw [comp_normalizedSection (hxb i) hx' (xr i).hom (f i) (hxf i),
      comp_normalizedSection (hyb i) hy' (yr i).hom (f i) (hyf i)]
    simpa using (comp_normalizedSection (hxb i) (hyb i) (φ i) (𝟙 (V i)) (hφf' i)).symm
  have hb : yoneda.map (eqToHom hxy) ≫ y.sec = x.sec := by
    calc yoneda.map (eqToHom hxy) ≫ y.sec
        = yoneda.map (eqToHom hx') ≫ normalizedSection y hy' := by
          rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, eqToHom_trans]
      _ = yoneda.map (eqToHom hx') ≫ normalizedSection x hx' := by rw [hb']
      _ = x.sec := by
          rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, eqToHom_trans,
            eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp]
  have hp : e.hom ≫ normalizedProjection y hy' = normalizedProjection x hx' := by
    refine (Restriction.isJointlyLocallySurjective x hx V f hf xr).hom_ext
      (isAlgebraicSpace_yoneda 𝒞 S hS U).isSheaf fun i => ?_
    have hφp : Hom.map (φ i) ≫ normalizedProjection (yr i).pt (yr i).hpt =
        normalizedProjection (xr i).pt (xr i).hpt := by
      rw [(isPullback_normalizedProjection (hxb i) (hyb i) (φ i) (𝟙 (V i))
        (hφf' i)).w, CategoryTheory.Functor.map_id, Category.comp_id]
    rw [← Category.assoc, he, Category.assoc, (Restriction.isPullback y hy (f i) (yr i)).w,
      ← Category.assoc, hφp, ← (Restriction.isPullback x hx (f i) (xr i)).w]
  have hw : e.hom ≫ y.total.hom = x.total.hom ≫ yoneda.map (eqToHom hxy) := by
    apply (cancel_mono (yoneda.map (eqToHom hy'))).1
    calc (e.hom ≫ y.total.hom) ≫ yoneda.map (eqToHom hy')
        = e.hom ≫ normalizedProjection y hy' := Category.assoc _ _ _
      _ = normalizedProjection x hx' := hp
      _ = (x.total.hom ≫ yoneda.map (eqToHom hxy)) ≫ yoneda.map (eqToHom hy') := by
          rw [Category.assoc, ← CategoryTheory.Functor.map_comp, eqToHom_trans]
  have hs : actionMap x ≫ e.hom =
      actionBaseChange (eqToHom hxy) hb e.hom hw.symm ≫ actionMap y := by
    refine (Restriction.isJointlyLocallySurjective_action x hx V f hf xr).hom_ext
      y.isAlgebraicSpace.isSheaf fun i => ?_
    have h4 : actionBaseChange (Hom.base (xr i).hom) (Hom.comp_sec (xr i).hom)
          (Hom.map (xr i).hom) (Hom.isPullback (xr i).hom).w.symm ≫
          actionBaseChange (eqToHom hxy) hb e.hom hw.symm =
        actionBaseChange (Hom.base (φ i)) (Hom.comp_sec (φ i)) (Hom.map (φ i))
            (Hom.isPullback (φ i)).w.symm ≫
          actionBaseChange (Hom.base (yr i).hom) (Hom.comp_sec (yr i).hom)
            (Hom.map (yr i).hom) (Hom.isPullback (yr i).hom).w.symm := by
      rw [actionBaseChange_comp, actionBaseChange_comp]
      exact actionBaseChange_congr (hfac i) (he i)
    have s₁ : actionMap (xr i).pt ≫ Hom.map (xr i).hom =
        actionBaseChange (Hom.base (xr i).hom) (Hom.comp_sec (xr i).hom)
          (Hom.map (xr i).hom) (Hom.isPullback (xr i).hom).w.symm ≫ actionMap x :=
      Hom.smul_comp (xr i).hom
    have s₂ : actionMap (xr i).pt ≫ Hom.map (φ i) =
        actionBaseChange (Hom.base (φ i)) (Hom.comp_sec (φ i)) (Hom.map (φ i))
          (Hom.isPullback (φ i)).w.symm ≫ actionMap (yr i).pt :=
      Hom.smul_comp (φ i)
    have s₃ : actionMap (yr i).pt ≫ Hom.map (yr i).hom =
        actionBaseChange (Hom.base (yr i).hom) (Hom.comp_sec (yr i).hom)
          (Hom.map (yr i).hom) (Hom.isPullback (yr i).hom).w.symm ≫ actionMap y :=
      Hom.smul_comp (yr i).hom
    calc _ = (actionMap (xr i).pt ≫ Hom.map (xr i).hom) ≫ e.hom := by
          rw [s₁, Category.assoc]
      _ = (actionMap (xr i).pt ≫ Hom.map (φ i)) ≫ Hom.map (yr i).hom := by
          rw [Category.assoc, he i, Category.assoc]
      _ = _ := by
          rw [s₂, Category.assoc, s₃, ← Category.assoc, ← h4, Category.assoc]
  exact ⟨⟨eqToHom hxy, hb, e.hom, IsPullback.of_horiz_isIso ⟨hw⟩, hs⟩, rfl, rfl,
    fun i => Hom.ext (hfac i) (he i)⟩

variable (hB G P) in
/-- Condition (2) of Stacks 02ZI for the projection `p : TorsorsFor hB G P ⥤ (Sch/S)_fppf`, for
every covering property `P`: for two torsors over the same object `U` of the big fppf site of
`S`, a family of isomorphisms of their restrictions along a covering family of `U` which agree on
the overlaps glues, uniquely, to an isomorphism over `U`. -/
theorem projection_isomIsSheaf :
    ∀ {U : BigFppfOver 𝒞 S hS} (x y : TorsorsFor hB G P)
      (hx : (projection hB G P).obj x = U) (hy : (projection hB G P).obj y = U)
      {I : Type w} (V : I → BigFppfOver 𝒞 S hS) (f : ∀ i, V i ⟶ U),
      Sieve.ofArrows V f ∈ BigFppfOver.topology 𝒞 S hS U →
      ∀ (Vij : I → I → BigFppfOver 𝒞 S hS)
        (pr₁ : ∀ i j, Vij i j ⟶ V i) (pr₂ : ∀ i j, Vij i j ⟶ V j)
        (hVij : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j))
        (xr : ∀ i, Functor.Restriction (projection hB G P) (f i) x hx)
        (yr : ∀ i, Functor.Restriction (projection hB G P) (f i) y hy)
        (xrij : ∀ i j, Functor.Restriction (projection hB G P) (pr₁ i j ≫ f i) x hx)
        (yrij : ∀ i j, Functor.Restriction (projection hB G P) (pr₁ i j ≫ f i) y hy),
        Functor.IsomIsSheafFor (projection hB G P) x y hx hy V f Vij pr₁ pr₂ hVij xr yr
          xrij yrij := by
  intro U x y hx hy I V f hf Vij pr₁ pr₂ hVij xr yr xrij yrij φ hφ _ hc
  obtain ⟨e, he⟩ :=
    Restriction.exists_glued_iso x y hx hy V f hf Vij pr₁ pr₂ hVij xr yr xrij yrij φ hφ hc
  have hxy : x.base = y.base := hx.trans hy.symm
  obtain ⟨g, hgf, -, hg⟩ :=
    Restriction.exists_glued_hom x y hx hy hxy V f hf xr yr φ hφ e he
  have hgLift : Functor.FibreHom (projection hB G P) x y hx hy g := by
    show (projection hB G P).IsHomLift (eqToHom hx ≫ eqToHom hy.symm) g
    have hmap : eqToHom hx ≫ eqToHom hy.symm = (projection hB G P).map g := by
      rw [eqToHom_trans]
      exact hgf.symm
    rw [hmap]
    exact CategoryTheory.IsHomLift.map _ _
  have : IsIso (Hom.base g) := by
    rw [hgf]
    infer_instance
  refine ⟨g, ⟨hgLift, isIso_of_isIso_base g, hg⟩, ?_⟩
  rintro k ⟨hk, -, hkg⟩
  have hkb : Hom.base k = eqToHom hx ≫ eqToHom hy.symm := base_eq_of_isHomLift k _ hk
  exact Hom.ext (hkb.trans ((eqToHom_trans _ _).trans hgf.symm)) <|
    (Restriction.isJointlyLocallySurjective x hx V f hf xr).hom_ext
      y.isAlgebraicSpace.isSheaf fun i => congrArg Hom.map ((hkg i).trans (hg i).symm)

end TorsorsFor

end AlgebraicGeometry.Space

end
