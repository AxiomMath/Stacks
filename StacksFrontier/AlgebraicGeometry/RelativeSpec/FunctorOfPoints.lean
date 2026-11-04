module

public import Mathlib.AlgebraicGeometry.Sites.Representability
public import StacksFrontier.AlgebraicGeometry.RelativeSpecRepresentability.Basic

/-!
# The functor of points of a relative spectrum

Let `X` be a scheme and let `A` be a quasi-coherent sheaf of commutative `𝒪_X`-algebras. The
relative spectrum of `A` is described by the contravariant functor sending a test scheme `T` to
the set of pairs `(f, φ)` consisting of a morphism of schemes `f : T ⟶ X` and a morphism
`φ : A ⟶ f_* 𝒪_T` of sheaves of `𝒪_X`-algebras, a morphism of test schemes acting by pullback
of such pairs.

This file records how that functor behaves and gives the criterion by which a scheme over the
base is recognised as representing it. It then proves the two general facts about the functor
on which the representability argument of [Stacks, Tag 01LU] rests, neither of which mentions
base change of a quasi-coherent algebra: the functor is a sheaf for the Zariski topology on
schemes, and a Zariski sheaf over the functor of points of a scheme is representable as soon as
its base change to each member of an open cover of that scheme is.

## Main results

* `Stacks.RelativeSpec.relativeSpecFunctor_map_apply`,
  `Stacks.RelativeSpec.RelativeSpecPair.pullback_fst` and
  `Stacks.RelativeSpec.RelativeSpecPair.pullback_snd_right` compute the functor and the two
  components of a pulled-back pair, and
  `Stacks.RelativeSpec.RelativeSpecPair.pullback_id` and
  `Stacks.RelativeSpec.RelativeSpecPair.pullback_comp` are the functoriality of pullback.
* `Stacks.RelativeSpec.representableByOfBijective`: a pair over a scheme `Y` whose pullback map
  `(T ⟶ Y) → {(f, φ) over T}` is bijective for every test scheme `T` exhibits `Y` as
  representing the functor.
* `Stacks.RelativeSpec.universalPair` is the converse datum, the pair over a representing
  scheme obtained from the identity morphism;
  `Stacks.RelativeSpec.homEquiv_eq_pullback_universalPair` says that every pair over a test
  scheme is the pullback of this one along a unique morphism, and
  `Stacks.RelativeSpec.bijective_pullback_universalPair` is that uniqueness and existence as a
  bijection.
* `Stacks.RelativeSpecFunctorOfPoints.relativeSpecFunctor_isSheaf`: the relative-spectrum
  functor of a quasi-coherent algebra is a Zariski sheaf.
* `Stacks.RelativeSpecFunctorOfPoints.isRepresentable_of_representablePullbacks`: a Zariski
  sheaf `F` equipped with a morphism `π : F ⟶ yoneda.obj S` is representable once each fibre
  product of `yoneda.obj (U i)` with `F` over `yoneda.obj S` is, for `U` an open cover of `S`.

## Implementation notes

A morphism `φ : A ⟶ f_* 𝒪_T` of sheaves of `𝒪_X`-algebras is recorded as a morphism in the
category of presheaves of commutative rings under `𝒪_X`, from the structure morphism of `A` to
the comorphism of `f`. This loses nothing: a morphism of sheaves is a morphism of the
underlying presheaves, and for commutative rings an algebra map is exactly a ring map
commuting with the two structure morphisms.

The source of the Stacks tag describes `φ` instead as a morphism of `𝒪_T`-algebras
`f^*A ⟶ 𝒪_T`, and notes that the two descriptions, together with the description by
`f^{-1}𝒪_S`-algebra maps `f^{-1}A ⟶ 𝒪_T`, carry the same data.

The sheaf property is proved by gluing on the level of presheafed spaces. A relative-spectrum
pair `(f, φ)` over `T` is the same thing as a morphism of presheafed spaces from `T` to the
pair `(S, A)` whose composite with the structural map of `(S, A)` is `f`. Morphisms of
presheafed spaces glue along an open cover of a scheme because the forgetful functor from
schemes to presheafed spaces preserves the relevant pullbacks and carries the glued cover to a
colimit.

Local representability is `AlgebraicGeometry.Scheme.LocalRepresentability.isRepresentable`
applied to the coproduct of the representing objects of the base changes. The content of the
argument is that the induced map out of that coproduct is locally surjective, which is checked
on the pullback cover of a test scheme.

Together with representability over an affine base
(`Stacks.RelativeSpec.relativeSpecFunctor_representableBy`, Tag 01LT) and the base-change
description of Tag 01LS, the two results of the second half give one proof of Tag 01LU. This
library proves Tag 01LU instead by gluing the affine spectra directly; that is
`Stacks.RelativeSpec.relativeSpecFunctor_isRepresentable`.

Every rewrite the geometric arguments need has to match through the bundled projections of a
`Scheme.Cover` (its index type) and of `PresheafedSpace` (the image of the forgetful functor
against `Scheme.toPresheafedSpace`), and the resulting goals are not type-correct at
`implicit` transparency, so the rewrites fail. The `Abstract` section below therefore restates
each of those steps as a lemma about an arbitrary category or functor, in which the composites
appear as named hypotheses; the geometric proofs apply them as terms and the identifications
are then discharged during elaboration.

## References

* [Stacks Project, Tag 01LR](https://stacks.math.columbia.edu/tag/01LR)
* [Stacks Project, Tag 01LU](https://stacks.math.columbia.edu/tag/01LU)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

universe u v

namespace Stacks.RelativeSpec

add_to_stacks 01LR relativeSpecFunctor

variable {s : RelativeSpecSituation.{u}} {T T' T'' Y : Scheme.{u}}

/-- The functor of points of a relative spectrum acts on a morphism of test schemes by pullback
of pairs. -/
theorem relativeSpecFunctor_map_apply (a : T' ⟶ T) (p : RelativeSpecPair s T) :
    (relativeSpecFunctor s).map a.op p = RelativeSpecPair.pullback a p :=
  rfl

/-- The morphism of schemes underlying a pulled-back pair. -/
@[simp]
theorem RelativeSpecPair.pullback_fst (a : T' ⟶ T) (p : RelativeSpecPair s T) :
    (RelativeSpecPair.pullback a p).1 = a ≫ p.1 :=
  rfl

/-- The morphism of sheaves underlying a pulled-back pair: the morphism of the original pair
followed by the pushforward of the comorphism of `a`. -/
@[simp]
theorem RelativeSpecPair.pullback_snd_right (a : T' ⟶ T) (p : RelativeSpecPair s T) :
    (RelativeSpecPair.pullback a p).2.right =
      p.2.right ≫ (TopCat.Presheaf.pushforward CommRingCat p.1.base).map a.c :=
  rfl

/-- Pulling a pair back along the identity leaves it unchanged. -/
@[simp]
theorem RelativeSpecPair.pullback_id (p : RelativeSpecPair s T) :
    RelativeSpecPair.pullback (𝟙 T) p = p :=
  (relativeSpecFunctor s).map_id_apply (op T) p

/-- Pulling a pair back along a composite is pulling it back along each factor in turn. -/
theorem RelativeSpecPair.pullback_comp (b : T'' ⟶ T') (a : T' ⟶ T) (p : RelativeSpecPair s T) :
    RelativeSpecPair.pullback (b ≫ a) p =
      RelativeSpecPair.pullback b (RelativeSpecPair.pullback a p) :=
  (relativeSpecFunctor s).map_comp_apply a.op b.op p

/-- A pair over `Y` whose pullback map is a bijection at every test scheme exhibits `Y` as
representing the functor of points of the relative spectrum. -/
def representableByOfBijective (p : RelativeSpecPair s Y)
    (h : ∀ T : Scheme.{u}, Function.Bijective fun g : T ⟶ Y ↦ RelativeSpecPair.pullback g p) :
    (relativeSpecFunctor s).RepresentableBy Y where
  homEquiv {T} := Equiv.ofBijective _ (h T)
  homEquiv_comp b a := RelativeSpecPair.pullback_comp b a p

/-- The universal pair over a scheme representing the functor of points of a relative spectrum:
the pair corresponding to the identity morphism. Its first component is the structure morphism
to the base and its second component is the universal morphism of algebras. -/
def universalPair (h : (relativeSpecFunctor s).RepresentableBy Y) : RelativeSpecPair s Y :=
  h.homEquiv (𝟙 Y)

/-- Over a representing scheme, the bijection with morphisms into it is pullback of the
universal pair. -/
theorem homEquiv_eq_pullback_universalPair (h : (relativeSpecFunctor s).RepresentableBy Y)
    (g : T ⟶ Y) : h.homEquiv g = RelativeSpecPair.pullback g (universalPair h) := by
  have hc := h.homEquiv_comp g (𝟙 Y)
  rwa [Category.comp_id] at hc

/-- Every pair over a test scheme is the pullback of the universal pair along a unique morphism
to the representing scheme. -/
theorem bijective_pullback_universalPair (h : (relativeSpecFunctor s).RepresentableBy Y)
    (T : Scheme.{u}) :
    Function.Bijective fun g : T ⟶ Y ↦ RelativeSpecPair.pullback g (universalPair h) := by
  have hfun : (fun g : T ⟶ Y ↦ RelativeSpecPair.pullback g (universalPair h)) =
      fun g : T ⟶ Y ↦ h.homEquiv g :=
    funext fun g ↦ (homEquiv_eq_pullback_universalPair h g).symm
  rw [hfun]
  exact h.homEquiv.bijective

end Stacks.RelativeSpec

namespace Stacks.RelativeSpecFunctorOfPoints

open CategoryTheory.Limits

/-! ### Abstract categorical helpers

Every lemma in this section is stated for an arbitrary category or functor. They are the
reformulations that let the geometric arguments below be written as terms: a `rw` inside the
geometric goals has to match through the bundled projections of a `Scheme.Cover` and of
`PresheafedSpace`, which is not type-correct at `implicit` transparency, whereas naming the
composites as hypotheses of an abstract lemma discharges the same identifications during
elaboration.
-/

section Abstract

variable {C : Type*} [Category C]

/-- Cancel an isomorphism on the right of a known factorisation. -/
theorem comp_inv_eq_of_comp_eq {X Y Z : C} {a : X ⟶ Y} {h : Y ⟶ Z} [IsIso h] {b : X ⟶ Z}
    (w : a ≫ h = b) : b ≫ inv h = a := by
  rw [← w, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-- Reassociate against a known factorisation of the first two legs. -/
theorem comp_comp_of_comp_eq {W X Y Z : C} {a : W ⟶ X} {b : X ⟶ Y} {m : W ⟶ Y}
    (w : a ≫ b = m) (c : Y ⟶ Z) : a ≫ b ≫ c = m ≫ c := by
  rw [← w, Category.assoc]

/-- Cancel the inverse of an isomorphism against a known factorisation through it. -/
theorem comp_inv_comp_of_comp_eq {W X Y Z : C} {m : W ⟶ X} {e : X ≅ Y} {k : W ⟶ Y}
    (w : m ≫ e.hom = k) (c : X ⟶ Z) : k ≫ e.inv ≫ c = m ≫ c := by
  rw [← w, Category.assoc, Iso.hom_inv_id_assoc]

/-- Cancel an isomorphism occurring as `inv` then `hom`. -/
theorem comp_inv_comp_hom_comp {W X Y Z : C} (a : W ⟶ Y) (e : X ≅ Y) (c : Y ⟶ Z) :
    (a ≫ e.inv) ≫ e.hom ≫ c = a ≫ c := by
  rw [Category.assoc, Iso.inv_hom_id_assoc]

/-- Transpose an isomorphism across an equation, the direction of `Iso.inv_comp_eq`. -/
theorem eq_hom_comp_of_inv_comp_eq {W X Y : C} (e : W ≅ X) {g' : W ⟶ Y} {g : X ⟶ Y}
    (w : e.inv ≫ g' = g) : g' = e.hom ≫ g := by
  rw [← w, Iso.hom_inv_id_assoc]

variable {D : Type*} [Category D] (F : C ⥤ D)

/-- Transport an equality of morphisms through a functor, precomposed with a fixed morphism. -/
theorem map_comp_congr {A B : C} {Z : D} {uu vv : A ⟶ B} (h : uu = vv) (g : F.obj B ⟶ Z) :
    F.map vv ≫ g = F.map uu ≫ g := by rw [h]

/-- Transport an equality of two-step composites through a functor. -/
theorem map_comp_comp_eq {A B₁ B₂ E : C} (u₁ : A ⟶ B₁) (v₁ : B₁ ⟶ E) (u₂ : A ⟶ B₂)
    (v₂ : B₂ ⟶ E) (h : u₁ ≫ v₁ = u₂ ≫ v₂) {Z : D} (q : F.obj E ⟶ Z) :
    F.map u₁ ≫ F.map v₁ ≫ q = F.map u₂ ≫ F.map v₂ ≫ q := by
  rw [← F.map_comp_assoc, ← F.map_comp_assoc, h]

/-- Drop a trailing identity that has been transported through a functor. -/
theorem eq_of_comp_map_id {A : C} {Z : D} {x y : Z ⟶ F.obj A} (w : x = y ≫ F.map (𝟙 A)) :
    x = y := by rw [w, F.map_id, Category.comp_id]

/-- Evaluate a known factorisation of a natural transformation of `Type`-valued functors. -/
theorem natTrans_comp_apply {F₁ F₂ F₃ : Cᵒᵖ ⥤ Type v} {ι : F₁ ⟶ F₂} {d : F₂ ⟶ F₃}
    {η : F₁ ⟶ F₃} (w : ι ≫ d = η) (A : Cᵒᵖ) (x : F₁.obj A) :
    d.app A (ι.app A x) = η.app A x := by
  subst w; rfl

end Abstract

/-! ### Gluing morphisms of presheafed spaces along an open cover -/

private abbrev forgetToPresheafedSpace : Scheme.{u} ⥤ PresheafedSpace CommRingCat.{u} :=
  Scheme.forgetToLocallyRingedSpace ⋙ LocallyRingedSpace.forgetToSheafedSpace ⋙
    SheafedSpace.forgetToPresheafedSpace

/-- A compatible family of morphisms of presheafed spaces out of the members of an open cover
glues to a unique morphism out of the covered scheme. -/
private lemma existsUnique_gluePresheafedSpaceHom {T : Scheme.{u}} (𝒰 : T.OpenCover.{u})
    (Y : PresheafedSpace CommRingCat.{u})
    (f : ∀ i, (𝒰.X i).toPresheafedSpace ⟶ Y)
    (hf : ∀ i j, (pullback.fst (𝒰.f i) (𝒰.f j)).toPshHom ≫ f i =
      (pullback.snd (𝒰.f i) (𝒰.f j)).toPshHom ≫ f j) :
    ∃! g : T.toPresheafedSpace ⟶ Y, ∀ i, (𝒰.f i).toPshHom ≫ g = f i := by
  let D := 𝒰.gluedCover.toGlueData
  have : ∀ i j k, PreservesLimit (cospan (D.f i j) (D.f i k)) forgetToPresheafedSpace := by
    intro i j k
    show PreservesLimit _ (Scheme.forgetToLocallyRingedSpace ⋙ _)
    apply +allowSynthFailures Limits.comp_preservesLimit
    apply +allowSynthFailures preservesLimit_of_iso_diagram
    · exact (diagramIsoCospan _).symm
    · dsimp
      infer_instance
  let E := D.mapGlueData forgetToPresheafedSpace
  let e : T.toPresheafedSpace ≅ E.glued :=
    (forgetToPresheafedSpace.mapIso (asIso 𝒰.fromGlued)).symm ≪≫
      D.gluedIso forgetToPresheafedSpace
  have he (i) : (𝒰.f i).toPshHom ≫ e.hom = E.ι i := by
    have hi : 𝒰.f i ≫ inv 𝒰.fromGlued = D.ι i := comp_inv_eq_of_comp_eq (𝒰.ι_fromGlued i)
    exact (comp_comp_of_comp_eq
        (Functor.map_comp forgetToPresheafedSpace (𝒰.f i) (inv 𝒰.fromGlued)).symm
        (D.gluedIso forgetToPresheafedSpace).hom).trans
      ((map_comp_congr forgetToPresheafedSpace hi.symm _).trans
        (D.ι_gluedIso_hom forgetToPresheafedSpace i))
  have h (ij : E.J × E.J) :
      E.diagram.fst ij ≫ f ij.1 = E.diagram.snd ij ≫ f ij.2 :=
    (hf ij.1 ij.2).trans
      (map_comp_congr forgetToPresheafedSpace
        (pullbackSymmetry_hom_comp_fst (𝒰.f ij.1) (𝒰.f ij.2)) (f ij.2))
  let g := Multicoequalizer.desc E.diagram Y f h
  refine ⟨e.hom ≫ g, fun i => (comp_comp_of_comp_eq (he i) g).trans
    (Multicoequalizer.π_desc _ _ _ _ _), fun g' hg' => eq_hom_comp_of_inv_comp_eq e ?_⟩
  refine Multicoequalizer.hom_ext _ _ _ fun i => ?_
  exact ((comp_inv_comp_of_comp_eq (he i) g').trans (hg' i)).trans
    (Multicoequalizer.π_desc E.diagram Y f h i).symm

/-! ### The relative-spectrum functor is a Zariski sheaf -/

variable {s : Stacks.RelativeSpec.RelativeSpecSituation.{u}}

/-- The base of a relative-spectrum situation, carrying the algebra instead of its structure
sheaf, as a presheafed space. -/
private abbrev algebraPresheafedSpace (s : Stacks.RelativeSpec.RelativeSpecSituation.{u}) :
    PresheafedSpace CommRingCat.{u} := ⟨s.base.carrier, s.algebra.right.obj⟩

/-- The structural map of `algebraPresheafedSpace`, the identity on spaces and the structure
morphism of the algebra on presheaves. -/
private def algebraToBase (s : Stacks.RelativeSpec.RelativeSpecSituation.{u}) :
    algebraPresheafedSpace s ⟶ s.base.toPresheafedSpace :=
  ⟨𝟙 _, s.algebra.hom.hom⟩

/-- A relative-spectrum pair over `T`, read as a morphism of presheafed spaces from `T` to
`algebraPresheafedSpace`. -/
private def relativeSpecPair_toHom {T : Scheme.{u}}
    (p : Stacks.RelativeSpec.RelativeSpecPair s T) :
    T.toPresheafedSpace ⟶ algebraPresheafedSpace s :=
  ⟨p.1.base, p.2.right⟩

private lemma relativeSpecPair_toHom_comp {T : Scheme.{u}}
    (p : Stacks.RelativeSpec.RelativeSpecPair s T) :
    relativeSpecPair_toHom p ≫ algebraToBase s = p.1.toPshHom :=
  PresheafedSpace.hext _ _ rfl (heq_of_eq p.2.w)

private lemma relativeSpecPair_toHom_pullback {T T' : Scheme.{u}}
    (a : T' ⟶ T) (p : Stacks.RelativeSpec.RelativeSpecPair s T) :
    relativeSpecPair_toHom (Stacks.RelativeSpec.RelativeSpecPair.pullback a p) =
      a.toPshHom ≫ relativeSpecPair_toHom p := rfl

private lemma relativeSpecPair_toHom_eq_of_pullback_eq {T T₁ T₂ : Scheme.{u}} (a : T ⟶ T₁)
    (b : T ⟶ T₂) {p : Stacks.RelativeSpec.RelativeSpecPair s T₁}
    {q : Stacks.RelativeSpec.RelativeSpecPair s T₂}
    (h : Stacks.RelativeSpec.RelativeSpecPair.pullback a p =
      Stacks.RelativeSpec.RelativeSpecPair.pullback b q) :
    a.toPshHom ≫ relativeSpecPair_toHom p = b.toPshHom ≫ relativeSpecPair_toHom q := by
  simpa only [relativeSpecPair_toHom_pullback] using congrArg relativeSpecPair_toHom h

/-- Two morphisms of presheaves into the pushforward of the structure sheaf agree as soon as
their components agree up to the identity transported through the structure sheaf. -/
private lemma presheaf_hom_ext_of_app_eq {T : Scheme.{u}} {Z : TopCat.{u}} {b : T.carrier ⟶ Z}
    {A : Z.Presheaf CommRingCat.{u}}
    (x y : A ⟶ (TopCat.Presheaf.pushforward CommRingCat b).obj T.presheaf)
    (h : ∀ U, x.app U = y.app U ≫ T.presheaf.map (𝟙 _)) : x = y :=
  NatTrans.ext (funext fun U => eq_of_comp_map_id T.presheaf (h U))

private lemma relativeSpecPair_ext {T : Scheme.{u}}
    (p q : Stacks.RelativeSpec.RelativeSpecPair s T) (h : p.1 = q.1)
    (h' : relativeSpecPair_toHom p = relativeSpecPair_toHom q) : p = q := by
  rcases p with ⟨f, α⟩
  rcases q with ⟨g, β⟩
  dsimp at h
  subst g
  congr 1
  exact Under.UnderMorphism.ext (presheaf_hom_ext_of_app_eq _ _ (PresheafedSpace.congr_app h'))

private lemma relativeSpecPair_of_hom {T : Scheme.{u}}
    (f : T ⟶ s.base) (q : T.toPresheafedSpace ⟶ algebraPresheafedSpace s)
    (h : q ≫ algebraToBase s = f.toPshHom) :
    ∃ p : Stacks.RelativeSpec.RelativeSpecPair s T,
      p.1 = f ∧ relativeSpecPair_toHom p = q := by
  rcases q with ⟨b, c⟩
  have hb : b = f.base := congrArg PresheafedSpace.Hom.base h
  subst b
  exact ⟨⟨f, Under.homMk c (presheaf_hom_ext_of_app_eq _ _ (PresheafedSpace.congr_app h))⟩,
    rfl, rfl⟩

private lemma presheafedSpaceHom_ext {T : Scheme.{u}} (𝒰 : T.OpenCover.{u})
    {Y : PresheafedSpace CommRingCat.{u}} (q r : T.toPresheafedSpace ⟶ Y)
    (h : ∀ i, (𝒰.f i).toPshHom ≫ q = (𝒰.f i).toPshHom ≫ r) : q = r := by
  have hc (i j) : (pullback.fst (𝒰.f i) (𝒰.f j)).toPshHom ≫
      ((𝒰.f i).toPshHom ≫ q) = (pullback.snd (𝒰.f i) (𝒰.f j)).toPshHom ≫
      ((𝒰.f j).toPshHom ≫ q) :=
    map_comp_comp_eq forgetToPresheafedSpace (pullback.fst (𝒰.f i) (𝒰.f j)) (𝒰.f i)
      (pullback.snd (𝒰.f i) (𝒰.f j)) (𝒰.f j) pullback.condition q
  exact (existsUnique_gluePresheafedSpaceHom 𝒰 Y _ hc).unique (fun _ => rfl) (fun i => (h i).symm)

/-- Relative-spectrum pairs satisfy the gluing condition for an open cover of the test
scheme. -/
private lemma existsUnique_glueRelativeSpecPair {T : Scheme.{u}} (𝒰 : T.OpenCover.{u})
    (p : ∀ i, Stacks.RelativeSpec.RelativeSpecPair s (𝒰.X i))
    (hp : ∀ i j, Stacks.RelativeSpec.RelativeSpecPair.pullback
        (pullback.fst (𝒰.f i) (𝒰.f j)) (p i) =
      Stacks.RelativeSpec.RelativeSpecPair.pullback (pullback.snd (𝒰.f i) (𝒰.f j)) (p j)) :
    ∃! q : Stacks.RelativeSpec.RelativeSpecPair s T,
      ∀ i, Stacks.RelativeSpec.RelativeSpecPair.pullback (𝒰.f i) q = p i := by
  have hb (i j) : pullback.fst (𝒰.f i) (𝒰.f j) ≫ (p i).1 =
      pullback.snd (𝒰.f i) (𝒰.f j) ≫ (p j).1 := congrArg Sigma.fst (hp i j)
  let f := 𝒰.glueMorphisms (fun i => (p i).1) hb
  have hf (i) : 𝒰.f i ≫ f = (p i).1 := 𝒰.ι_glueMorphisms _ _ i
  obtain ⟨q, hq, _⟩ := existsUnique_gluePresheafedSpaceHom 𝒰 (algebraPresheafedSpace s)
    (fun i => relativeSpecPair_toHom (p i))
    (fun i j => relativeSpecPair_toHom_eq_of_pullback_eq _ _ (hp i j))
  have hqf : q ≫ algebraToBase s = f.toPshHom := presheafedSpaceHom_ext 𝒰 _ _ fun i => by
    rw [← Category.assoc, hq, relativeSpecPair_toHom_comp]
    exact (congrArg (fun k => forgetToPresheafedSpace.map k) (hf i)).symm
  obtain ⟨r, hr, hrq⟩ := relativeSpecPair_of_hom f q hqf
  have hri (i) : Stacks.RelativeSpec.RelativeSpecPair.pullback (𝒰.f i) r = p i := by
    apply relativeSpecPair_ext
    · show 𝒰.f i ≫ r.1 = _
      rw [hr, hf]
    · rw [relativeSpecPair_toHom_pullback, hrq, hq]
  refine ⟨r, hri, fun r' hr' => relativeSpecPair_ext _ _
    (𝒰.hom_ext _ _ fun i => (congrArg Sigma.fst (hr' i)).trans (congrArg Sigma.fst (hri i)).symm)
    (presheafedSpaceHom_ext 𝒰 _ _ fun i => ?_)⟩
  exact relativeSpecPair_toHom_eq_of_pullback_eq _ _ ((hr' i).trans (hri i).symm)

/-- The relative-spectrum functor of a quasi-coherent algebra is a sheaf for the Zariski
topology on schemes. -/
theorem relativeSpecFunctor_isSheaf (s : Stacks.RelativeSpec.RelativeSpecSituation.{u}) :
    Presheaf.IsSheaf Scheme.zariskiTopology (Stacks.RelativeSpec.relativeSpecFunctor s) := by
  rw [isSheaf_iff_isSheaf_of_type,
    Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange_of_small.{u}]
  intro T (𝒰 : T.OpenCover.{u})
  rw [Presieve.isSheafFor_arrows_iff_pullbacks]
  exact existsUnique_glueRelativeSpecPair 𝒰

/-! ### Local representability -/

/-- A Zariski sheaf with a morphism to the functor of points of a scheme is representable as
soon as its base change to each member of an open cover of that scheme is. -/
theorem isRepresentable_of_representablePullbacks
    (F : Sheaf Scheme.zariskiTopology.{u} (Type u)) {S : Scheme.{u}}
    (𝒰 : S.OpenCover.{u}) (π : F.obj ⟶ yoneda.obj S)
    (hrep : ∀ i : 𝒰.I₀, (pullback (yoneda.map (𝒰.f i)) π).IsRepresentable) :
    F.obj.IsRepresentable := by
  let P (i : 𝒰.I₀) := pullback (yoneda.map (𝒰.f i)) π
  have (i : 𝒰.I₀) : (P i).IsRepresentable := hrep i
  let X (i : 𝒰.I₀) := (P i).reprX
  let e (i : 𝒰.I₀) : yoneda.obj (X i) ≅ P i := (P i).reprW
  let η (i : 𝒰.I₀) : yoneda.obj (X i) ⟶ F.obj :=
    (e i).hom ≫ pullback.snd (yoneda.map (𝒰.f i)) π
  have hopen (i : 𝒰.I₀) : IsOpenImmersion.presheaf (η i) := by
    let := MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
      (P := @IsOpenImmersion)
    exact (IsOpenImmersion.presheaf.cancel_left_of_respectsIso (e i).hom _).mpr
      (IsOpenImmersion.presheaf.pullback_snd _ _ (MorphismProperty.relative_map (𝒰.map_prop i)))
  have hsurj : Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc η) := by
    constructor
    intro T p
    let f : T ⟶ S := π.app (op T) p
    let 𝒱 := 𝒰.pullback₁ f
    apply Scheme.zariskiTopology.superset_covering _ (Scheme.Cover.mem_grothendieckTopology 𝒱)
    apply (Sieve.generate_le_iff _ _).mpr
    rintro V a ⟨i⟩
    let b : yoneda.obj (𝒱.X i) ⟶ F.obj := yoneda.map (𝒱.f i) ≫ yonedaEquiv.symm p
    have hb : yoneda.map (pullback.snd f (𝒰.f i)) ≫ yoneda.map (𝒰.f i) = b ≫ π := by
      apply yonedaEquiv.injective
      show pullback.snd f (𝒰.f i) ≫ 𝒰.f i = π.app _ (F.obj.map (𝒱.f i).op p)
      exact pullback.condition.symm.trans
        (ConcreteCategory.congr_hom (π.naturality (𝒱.f i).op) p).symm
    let l : yoneda.obj (𝒱.X i) ⟶ P i :=
      pullback.lift (yoneda.map (pullback.snd f (𝒰.f i))) b hb
    let m : 𝒱.X i ⟶ X i := yonedaEquiv (l ≫ (e i).inv)
    have hm : (η i).app (op (𝒱.X i)) m = F.obj.map (𝒱.f i).op p :=
      congrArg yonedaEquiv ((comp_inv_comp_hom_comp l (e i)
        (pullback.snd (yoneda.map (𝒰.f i)) π)).trans (pullback.lift_snd _ _ hb))
    exact ⟨(Sigma.ι (fun i => yoneda.obj (X i)) i).app _ m,
      (natTrans_comp_apply (Sigma.ι_desc η i) _ m).trans hm⟩
  exact Scheme.LocalRepresentability.isRepresentable hopen

end Stacks.RelativeSpecFunctorOfPoints

end
