module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesPlusStrictlyFull
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.Groupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.Splittings
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothMonomorphismOpenImmersion

/-!
# The finite part as an open finite subgroupoid of a restriction

Let `(U, R, s, t, c)` be a groupoid in algebraic spaces over `B` with `s` and `t` separated and
locally of finite type, and let `(U', Z_univ, s', t', c')` be its finite part, with étale
projection `g : U' ⟶ U`. This file identifies `Z_univ` with an open subspace of the arrow space
of the restriction `R|_{U'}` whose restricted source and target are finite, that is, with an
open finite subgroupoid of `R|_{U'}`.

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.nonempty_openFiniteSubgroupoid_of_embedding`: a
  groupoid mapping to another by an isomorphism on objects and an open immersion on arrows, with
  finite source, is an open finite subgroupoid of the target.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.nonempty_openFiniteSubgroupoid_restrict`: the
  finite part of a groupoid in algebraic spaces is an open finite subgroupoid of the restriction
  along its étale projection.

## References

* [Stacks Project, Tag 025G](https://stacks.math.columbia.edu/tag/025G)
* [Stacks Project, Tag 03FV](https://stacks.math.columbia.edu/tag/03FV)
* [Stacks Project, Tag 044B](https://stacks.math.columbia.edu/tag/044B)
* [Stacks Project, Tag 04RK](https://stacks.math.columbia.edu/tag/04RK)
* [Stacks Project, Tag 04RU](https://stacks.math.columbia.edu/tag/04RU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

/-! ### Transporting a pointwise groupoid along bijections -/

/-- The map on presheaves of composable pairs induced by a map of groupoid data. -/
private def composableArrowsMap {J : Type w} [Category.{v} J] {U R U' R' : J ⥤ Type u}
    (s t : R ⟶ U) (s' t' : R' ⟶ U') (p : U ⟶ U') (q : R ⟶ R')
    (hs : q ≫ s' = s ≫ p) (ht : q ≫ t' = t ≫ p) :
    Deformation.composableArrows U R s t ⟶ Deformation.composableArrows U' R' s' t' where
  app T := ↾ fun a => ⟨(q.app T a.1.1, q.app T a.1.2), by
    have hs' := congrArg (fun f => f.app T a.1.1) hs
    have ht' := congrArg (fun f => f.app T a.1.2) ht
    exact hs'.trans ((congrArg (p.app T) a.2).trans ht'.symm)⟩
  naturality {A B} i := by
    ext a
    exact Subtype.ext (Prod.ext (q.naturality_apply i _) (q.naturality_apply i _))

/-- A groupoid structure on evaluated groupoid data transports along bijections of the objects
and of the arrows which match the source, target and composition maps. -/
private noncomputable def pointwiseGroupoidTransport
    {U R U' R' : Type u} {s t : R → U}
    {c : {p : R × R // s p.1 = t p.2} → R}
    (P : Deformation.PointwiseGroupoid s t c)
    (eu : U' ≃ U) (er : R' ≃ R) (s' t' : R' → U')
    (c' : {p : R' × R' // s' p.1 = t' p.2} → R')
    (hs : ∀ a, eu (s' a) = s (er a))
    (ht : ∀ a, eu (t' a) = t (er a))
    (hc : ∀ p, er (c' p) = c ⟨(er p.1.1, er p.1.2),
      (hs _).symm.trans ((congrArg eu p.2).trans (ht _))⟩) :
    Deformation.PointwiseGroupoid s' t' c' := by
  letI : Groupoid U := P.groupoid
  letI : Category U' := inferInstanceAs (Category (InducedCategory U eu))
  let G : Groupoid U' := Groupoid.ofFullyFaithfulToGroupoid
    (inducedFunctor eu) (fullyFaithfulInducedFunctor eu)
  refine { groupoid := G
           arrowEquiv := fun x y =>
             { toFun := fun f => ⟨er.symm (P.arrowEquiv _ _ f.hom).1, ?_, ?_⟩
               invFun := fun a => InducedCategory.homMk
                 ((P.arrowEquiv _ _).symm ⟨er a.1, ?_, ?_⟩)
               left_inv := ?_
               right_inv := ?_ }
           comp_eq := ?_ }
  · apply eu.injective
    rw [hs, er.apply_symm_apply]
    exact (P.arrowEquiv _ _ f.hom).2.1
  · apply eu.injective
    rw [ht, er.apply_symm_apply]
    exact (P.arrowEquiv _ _ f.hom).2.2
  · rw [← hs, a.2.1]
  · rw [← ht, a.2.2]
  · intro f
    apply InducedCategory.Hom.ext
    apply (P.arrowEquiv _ _).injective
    dsimp only [InducedCategory.homMk]
    rw [Equiv.apply_symm_apply]
    apply Subtype.ext
    exact er.apply_symm_apply _
  · intro a
    apply Subtype.ext
    dsimp only [InducedCategory.homMk]
    rw [Equiv.apply_symm_apply]
    exact er.symm_apply_apply _
  · intro x y z g f
    apply er.injective
    change er (er.symm (P.arrowEquiv _ _ (g.hom ≫ f.hom)).1) = _
    refine (er.apply_symm_apply _).trans ((P.comp_eq g.hom f.hom).trans ?_)
    refine Eq.trans ?_ (hc _).symm
    apply congrArg c
    apply Subtype.ext
    change (_, _) = (er (er.symm _), er (er.symm _))
    exact Prod.ext (er.apply_symm_apply _).symm (er.apply_symm_apply _).symm

/-! ### The inverse arrow of a groupoid in functors -/

/-- The inverse of an arrow exchanges its source and its target. -/
private theorem inverseArrow_source_target {J : Type w} [Category.{v} J]
    (G : Deformation.GroupoidInFunctors.{w, v, u} J) (T : J) (a : G.arrows.obj T) :
    G.source.app T (Deformation.inverseArrow G T a) = G.target.app T a ∧
      G.target.app T (Deformation.inverseArrow G T a) = G.source.app T a :=
  (G.evaluationArrowEquiv T _ _ (Groupoid.inv
    ((G.evaluationArrowEquiv T _ _).symm ⟨a, rfl, rfl⟩))).2

/-- The inverse arrow, read through the evaluated groupoid at prescribed endpoints. -/
private theorem inverseArrow_eq {J : Type w} [Category.{v} J]
    (G : Deformation.GroupoidInFunctors.{w, v, u} J) (T : J) (a : G.arrows.obj T)
    (x y : G.Evaluation T)
    (hs : G.source.app T a = x) (ht : G.target.app T a = y) :
    Deformation.inverseArrow G T a =
      (G.evaluationArrowEquiv T y x (Groupoid.inv
        ((G.evaluationArrowEquiv T x y).symm ⟨a, hs, ht⟩))).1 := by
  subst hs ht
  rfl

/-- Taking the inverse arrow twice gives back the arrow. -/
private theorem inverseArrow_involutive {J : Type w} [Category.{v} J]
    (G : Deformation.GroupoidInFunctors.{w, v, u} J) (T : J) :
    Function.Involutive (Deformation.inverseArrow G T) := by
  intro a
  have hs := (inverseArrow_source_target G T a).1
  have ht := (inverseArrow_source_target G T a).2
  let f := (G.evaluationArrowEquiv T _ _).symm
    (⟨a, rfl, rfl⟩ : {r // G.source.app T r = G.source.app T a ∧
      G.target.app T r = G.target.app T a})
  have hi : (G.evaluationArrowEquiv T _ _).symm
      ⟨Deformation.inverseArrow G T a, hs, ht⟩ = Groupoid.inv f := by
    apply (G.evaluationArrowEquiv T _ _).injective
    rw [Equiv.apply_symm_apply]
    rfl
  rw [inverseArrow_eq G T _ _ _ hs ht, hi]
  simp only [Groupoid.inv_eq_inv, IsIso.inv_inv]
  exact congrArg Subtype.val ((G.evaluationArrowEquiv T _ _).apply_symm_apply _)

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- The target morphism of a groupoid in algebraic spaces is finite as soon as its source
morphism is. -/
theorem isFinite_target_of_isFinite_source (G : GroupoidInAlgebraicSpaces C S hS B)
    (hs : Space.IsFinite C S hS G.source.hom) :
    Space.IsFinite C S hS G.target.hom := by
  obtain ⟨i, hi, -⟩ := Deformation.existsUnique_inverse G.toGroupoidInFunctors
  have hii : i ≫ i = 𝟙 _ := by
    ext T a
    show i.app T (i.app T a) = a
    rw [hi, hi]
    exact inverseArrow_involutive G.toGroupoidInFunctors T a
  let e : G.arrows.obj ≅ G.arrows.obj := ⟨i, i, hii, hii⟩
  have his : e.hom ≫ G.source.hom = G.target.hom := by
    ext T a
    show G.source.hom.app T (i.app T a) = G.target.hom.app T a
    exact (congrArg (G.source.hom.app T) (hi T a)).trans
      (inverseArrow_source_target G.toGroupoidInFunctors T a).1
  rw [← his]
  exact Space.isFinite_precomp_iso C S hS e G.source.hom hs

/-! ### Recognizing an open finite subgroupoid -/

/-- Two arrows of a groupoid in functors with the same endpoints and the same image under a
pointwise fully faithful morphism of groupoids are equal. -/
private theorem arrow_ext_of_fullyFaithful {J : Type w} [Category.{v} J]
    {H G : Deformation.GroupoidInFunctors.{w, v, u} J}
    (f : H.Hom G) (T : J) (hf : (f.evaluation T).FullyFaithful)
    {a b : H.arrows.obj T}
    (hs : H.source.app T a = H.source.app T b)
    (ht : H.target.app T a = H.target.app T b)
    (hm : f.mapArrows.app T a = f.mapArrows.app T b) : a = b := by
  let e := H.evaluationArrowEquiv T (H.source.app T a) (H.target.app T a)
  let x := e.symm ⟨a, rfl, rfl⟩
  let y := e.symm ⟨b, hs.symm, ht.symm⟩
  have he : (f.evaluation T).map x = (f.evaluation T).map y := by
    apply (G.evaluationArrowEquiv T _ _).injective
    apply Subtype.ext
    simpa only [f.evaluation_map_arrow, x, y, e, Equiv.apply_symm_apply] using hm
  simpa only [x, y, Equiv.apply_symm_apply] using congrArg (fun k => (e k).1) (hf.map_injective he)

/-- A map of groupoid data compatible with a pointwise fully faithful morphism to a common
groupoid preserves composition. -/
private theorem preserves_comp_of_fullyFaithful {J : Type w} [Category.{v} J]
    (H G K : Deformation.GroupoidInFunctors.{w, v, u} J)
    (f : H.Hom K) (g : G.Hom K)
    (hg : ∀ T, Nonempty (g.evaluation T).FullyFaithful)
    (p : H.objects ⟶ G.objects) (q : H.arrows ⟶ G.arrows)
    (hs : q ≫ G.source = H.source ≫ p)
    (ht : q ≫ G.target = H.target ≫ p)
    (_ho : p ≫ g.mapObjects = f.mapObjects)
    (ha : q ≫ g.mapArrows = f.mapArrows)
    (T : J) (a b : H.arrows.obj T) (h : H.source.app T a = H.target.app T b) :
    q.app T (H.compose T a b h) =
      G.compose T (q.app T a) (q.app T b)
        ((congrArg (fun k => k.app T a) hs).trans
          ((congrArg (p.app T) h).trans
            (congrArg (fun k => k.app T b) ht).symm)) := by
  classical
  refine arrow_ext_of_fullyFaithful g T (Classical.choice (hg T)) ?_ ?_ ?_
  · rw [functorGroupoid_comp_source G T _ _ _]
    show (q ≫ G.source).app T _ = (q ≫ G.source).app T _
    rw [hs]
    show p.app T (H.source.app T _) = p.app T (H.source.app T b)
    rw [functorGroupoid_comp_source H T a b h]
  · rw [functorGroupoid_comp_target G T _ _ _]
    show (q ≫ G.target).app T _ = (q ≫ G.target).app T _
    rw [ht]
    show p.app T (H.target.app T _) = p.app T (H.target.app T a)
    rw [functorGroupoid_comp_target H T a b h]
  · rw [← g.map_comp]
    show (q ≫ g.mapArrows).app T _ = _
    rw [ha, ← f.map_comp]
    have he (r : H.arrows.obj T) : g.mapArrows.app T (q.app T r) = f.mapArrows.app T r :=
      congrArg (fun k => k.app T r) ha
    simp only [he]

/-- A groupoid in algebraic spaces which maps to another by an isomorphism on objects and an
open immersion on arrows, compatibly with the source, target and composition, is an open finite
subgroupoid of the target as soon as its source morphism is finite. -/
theorem nonempty_openFiniteSubgroupoid_of_embedding
    (H G : GroupoidInAlgebraicSpaces C S hS B)
    (p : H.objects.obj ≅ G.objects.obj) (q : H.arrows.obj ⟶ G.arrows.obj) [Mono q]
    (hs : q ≫ G.source.hom = H.source.hom ≫ p.hom)
    (ht : q ≫ G.target.hom = H.target.hom ≫ p.hom)
    (hc : ∀ T (a b : H.arrows.obj.obj T) (h : H.source.hom.app T a = H.target.hom.app T b),
      q.app T (H.toGroupoidInFunctors.compose T a b h) =
        G.toGroupoidInFunctors.compose T (q.app T a) (q.app T b)
          ((congrArg (fun f => f.app T a) hs).trans
            ((congrArg (p.hom.app T) h).trans
              (congrArg (fun f => f.app T b) ht).symm)))
    (hq : Space.IsOpenImmersion C S hS q)
    (hf : Space.IsFinite C S hS H.source.hom) :
    Nonempty (OpenFiniteSubgroupoid G) := by
  let A := Subfunctor.range q
  let e : H.arrows.obj ≅ A.toFunctor := asIso (Subfunctor.toRange q)
  have he : e.hom ≫ A.ι = q := Subfunctor.toRange_ι q
  have hs' : e.inv ≫ H.source.hom = (A.ι ≫ G.source.hom) ≫ p.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← Category.assoc, he, hs]
    simp
  have ht' : e.inv ≫ H.target.hom = (A.ι ≫ G.target.hom) ≫ p.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← Category.assoc, he, ht]
    simp
  let cmp := composableArrowsMap (A.ι ≫ G.source.hom) (A.ι ≫ G.target.hom)
    H.source.hom H.target.hom p.inv e.inv hs' ht' ≫ H.toGroupoidInFunctors.comp ≫ e.hom
  have hsf : A.ι ≫ G.source.hom = e.inv ≫ H.source.hom ≫ p.hom := by
    rw [← Category.assoc, hs', Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have htf : A.ι ≫ G.target.hom = e.inv ≫ H.target.hom ≫ p.hom := by
    rw [← Category.assoc, ht', Category.assoc, Iso.inv_hom_id, Category.comp_id]
  refine ⟨{ arrows := A
            arrows_open := ⟨Space.isAlgebraicSpace_of_iso C S hS e H.arrows.property, ?_⟩
            source_finite := ?_
            target_finite := ?_
            comp := cmp
            comp_restricts := ?_
            pointwiseGroupoid := ?_ }⟩
  · have hι : A.ι = e.inv ≫ q := by rw [← he]; simp
    rw [hι]
    exact MorphismProperty.RespectsIso.precomp _ e.inv q hq
  · rw [hsf]
    exact Space.isFinite_precomp_iso C S hS e.symm _
      (Space.isFinite_postcomp_iso C S hS _ p hf)
  · rw [htf]
    exact Space.isFinite_precomp_iso C S hS e.symm _
      (Space.isFinite_postcomp_iso C S hS _ p
        (isFinite_target_of_isFinite_source H hf))
  · intro T a
    have he' (x : A.toFunctor.obj T) : q.app T (e.inv.app T x) = x.1 := by
      show (e.inv ≫ q).app T x = _
      rw [← he]
      simp
    show (e.hom ≫ A.ι).app T _ = _
    rw [he]
    let b := (composableArrowsMap (A.ι ≫ G.source.hom) (A.ι ≫ G.target.hom)
      H.source.hom H.target.hom p.inv e.inv hs' ht').app T a
    show q.app T (H.toGroupoidInFunctors.compose T b.1.1 b.1.2 b.2) = _
    rw [hc]
    show G.toGroupoidInFunctors.compose T (q.app T (e.inv.app T a.1.1))
      (q.app T (e.inv.app T a.1.2)) _ = _
    simp only [he']
    rfl
  · intro T
    refine ⟨pointwiseGroupoidTransport (H.toGroupoidInFunctors.pointwiseData T)
      ((p.symm.app T).toEquiv) ((e.symm.app T).toEquiv)
      ((A.ι ≫ G.source.hom).app T) ((A.ι ≫ G.target.hom).app T)
      (fun a => cmp.app T a) (fun a => (congrArg (fun f => f.app T a) hs').symm)
      (fun a => (congrArg (fun f => f.app T a) ht').symm) ?_⟩
    intro a
    show (e.hom ≫ e.inv).app T _ = _
    simp only [e.hom_inv_id, NatTrans.id_app]
    rfl

/-! ### The finite part inside the restriction -/

/-- The finite part of a groupoid in algebraic spaces, presented as a groupoid `H` with a
morphism to `G` whose arrow space is a finite open subspace `Z` of `G.arrows` over the object
space of `H`, is an open finite subgroupoid of the restriction of `G` along `Z.toBase`. -/
theorem nonempty_openFiniteSubgroupoid_restrict
    (G H : GroupoidInAlgebraicSpaces C S hS B)
    (f : Deformation.GroupoidInFunctors.Hom H.toGroupoidInFunctors G.toGroupoidInFunctors)
    (Z : Space.FiniteOpenSubspace C S hS G.source H.objects)
    (ho : Z.toBase.hom = f.mapObjects)
    (hg : Space.IsEtale C S hS Z.toBase.hom)
    (he : H.arrows.obj = Z.subspace.toFunctor)
    (hsource : H.source.hom = eqToHom he ≫ Z.subspace.ι ≫
      pullback.fst Z.toBase.hom G.source.hom)
    (hmap : f.mapArrows = eqToHom he ≫ Z.subspace.ι ≫
      pullback.snd Z.toBase.hom G.source.hom) :
    Nonempty (OpenFiniteSubgroupoid (restrict G Z.toBase).groupoid) := by
  classical
  let g : H.objects ⟶ G.objects := Z.toBase
  let Rst := restrict G g
  let fA : H.arrows ⟶ G.arrows := ObjectProperty.homMk f.mapArrows
  have hs : f.mapArrows ≫ G.source.hom = H.source.hom ≫ g.hom := by
    ext T a
    exact (f.map_source T a).trans (congrArg (fun k => k.app T (H.source.hom.app T a)) ho.symm)
  have ht : f.mapArrows ≫ G.target.hom = H.target.hom ≫ g.hom := by
    ext T a
    exact (f.map_target T a).trans (congrArg (fun k => k.app T (H.target.hom.app T a)) ho.symm)
  have hsA : fA ≫ G.source = H.source ≫ g := ObjectProperty.hom_ext _ hs
  have htA : fA ≫ G.target = H.target ≫ g := ObjectProperty.hom_ext _ ht
  let P1 := AlgebraicSpaces.isPullback_fiberProduct C S hS g G.target
  let P2 := AlgebraicSpaces.isPullback_fiberProduct C S hS G.source g
  let P3 := AlgebraicSpaces.isPullback_fiberProduct C S hS
    (fiberProductSnd g G.target) (fiberProductFst G.source g)
  let lA := P1.lift H.target fA htA.symm
  let mA := P2.lift fA H.source hsA
  have hlfst : lA ≫ fiberProductFst g G.target = H.target := P1.lift_fst _ _ _
  have hlsnd : lA ≫ fiberProductSnd g G.target = fA := P1.lift_snd _ _ _
  have hmfst : mA ≫ fiberProductFst G.source g = fA := P2.lift_fst _ _ _
  have hmsnd : mA ≫ fiberProductSnd G.source g = H.source := P2.lift_snd _ _ _
  let rA : H.arrows ⟶ restrictionArrows G g := P3.lift lA mA (by rw [hlsnd, hmfst])
  have hrfst : rA ≫ fiberProductFst (fiberProductSnd g G.target)
      (fiberProductFst G.source g) = lA := P3.lift_fst _ _ _
  have hrsnd : rA ≫ fiberProductSnd (fiberProductSnd g G.target)
      (fiberProductFst G.source g) = mA := P3.lift_snd _ _ _
  have hrsA : rA ≫ restrictionSource G g = H.source := by
    rw [← hmsnd, ← hrsnd]
    exact (Category.assoc _ _ _).symm
  have hrtA : rA ≫ restrictionTarget G g = H.target := by
    rw [← hlfst, ← hrfst]
    exact (Category.assoc _ _ _).symm
  have hraA : rA ≫ restrictionArrowsToArrows G g = fA := by
    rw [← hlsnd, ← hrfst]
    exact (Category.assoc _ _ _).symm
  let euA : H.objects ≅ Rst.groupoid.objects := eqToIso Rst.objects_eq.symm
  let qA : H.arrows ⟶ Rst.groupoid.arrows := rA ≫ eqToHom Rst.arrows_eq.symm
  have hcancelA : (eqToHom Rst.arrows_eq.symm :
      restrictionArrows G g ⟶ Rst.groupoid.arrows) ≫ eqToHom Rst.arrows_eq = 𝟙 _ := by
    rw [eqToHom_trans, eqToHom_refl]
  have hcancelO : euA.hom ≫ eqToHom Rst.objects_eq = 𝟙 H.objects := by
    simp only [euA, eqToIso.hom, eqToHom_trans, eqToHom_refl]
  have hqsA : qA ≫ Rst.groupoid.source = H.source ≫ euA.hom := by
    calc qA ≫ Rst.groupoid.source
        = (rA ≫ eqToHom Rst.arrows_eq.symm) ≫ (eqToHom Rst.arrows_eq ≫
            restrictionSource G g ≫ eqToHom Rst.objects_eq.symm) := by rw [Rst.source_eq]
      _ = rA ≫ (eqToHom Rst.arrows_eq.symm ≫ eqToHom Rst.arrows_eq) ≫
            (restrictionSource G g ≫ eqToHom Rst.objects_eq.symm) := by
          simp only [Category.assoc]
      _ = (rA ≫ restrictionSource G g) ≫ eqToHom Rst.objects_eq.symm := by
          rw [hcancelA, Category.id_comp, Category.assoc]
      _ = H.source ≫ euA.hom := by
          rw [hrsA]
          simp only [euA, eqToIso.hom]
  have hqtA : qA ≫ Rst.groupoid.target = H.target ≫ euA.hom := by
    calc qA ≫ Rst.groupoid.target
        = (rA ≫ eqToHom Rst.arrows_eq.symm) ≫ (eqToHom Rst.arrows_eq ≫
            restrictionTarget G g ≫ eqToHom Rst.objects_eq.symm) := by rw [Rst.target_eq]
      _ = rA ≫ (eqToHom Rst.arrows_eq.symm ≫ eqToHom Rst.arrows_eq) ≫
            (restrictionTarget G g ≫ eqToHom Rst.objects_eq.symm) := by
          simp only [Category.assoc]
      _ = (rA ≫ restrictionTarget G g) ≫ eqToHom Rst.objects_eq.symm := by
          rw [hcancelA, Category.id_comp, Category.assoc]
      _ = H.target ≫ euA.hom := by
          rw [hrtA]
          simp only [euA, eqToIso.hom]
  let p : H.objects.obj ≅ Rst.groupoid.objects.obj :=
    ⟨euA.hom.hom, euA.inv.hom, ObjectProperty.isoHom_inv_id_hom euA,
      ObjectProperty.isoInv_hom_id_hom euA⟩
  have hqs : qA.hom ≫ Rst.groupoid.source.hom = H.source.hom ≫ p.hom :=
    congrArg (fun k : H.arrows ⟶ Rst.groupoid.objects => k.hom) hqsA
  have hqt : qA.hom ≫ Rst.groupoid.target.hom = H.target.hom ≫ p.hom :=
    congrArg (fun k : H.arrows ⟶ Rst.groupoid.objects => k.hom) hqtA
  have hqo : p.hom ≫ Rst.hom.toGroupoidHom.mapObjects = f.mapObjects := by
    rw [Rst.mapObjects_eq, ← ho]
    calc p.hom ≫ (eqToHom Rst.objects_eq ≫ g).hom
        = ((euA.hom ≫ eqToHom Rst.objects_eq) ≫ g).hom := by
          simp only [p, ObjectProperty.FullSubcategory.comp_hom, Category.assoc]
      _ = g.hom := by
          rw [hcancelO, ObjectProperty.FullSubcategory.comp_hom,
            ObjectProperty.FullSubcategory.id_hom, Category.id_comp]
  have hqrA : qA ≫ eqToHom Rst.arrows_eq = rA := by
    simp only [qA, Category.assoc, hcancelA, Category.comp_id]
  have hqaA : qA ≫ (eqToHom Rst.arrows_eq ≫ restrictionArrowsToArrows G g) = fA := by
    rw [← Category.assoc, hqrA, hraA]
  have hqa : qA.hom ≫ Rst.hom.toGroupoidHom.mapArrows = f.mapArrows := by
    rw [Rst.mapArrows_eq]
    exact congrArg (fun k : H.arrows ⟶ G.arrows => k.hom) hqaA
  have hmfst' : mA.hom ≫ pullback.fst G.source.hom g.hom = f.mapArrows :=
    congrArg (fun k : H.arrows ⟶ G.arrows => k.hom) hmfst
  have hmsnd' : mA.hom ≫ pullback.snd G.source.hom g.hom = H.source.hom :=
    congrArg (fun k : H.arrows ⟶ H.objects => k.hom) hmsnd
  let sym := pullbackSymmetry g.hom G.source.hom
  have hzfst : (eqToHom he ≫ Z.subspace.ι ≫ sym.hom) ≫ pullback.fst G.source.hom g.hom =
      f.mapArrows := by
    rw [hmap, Category.assoc, Category.assoc, pullbackSymmetry_hom_comp_fst]
  have hzsnd : (eqToHom he ≫ Z.subspace.ι ≫ sym.hom) ≫ pullback.snd G.source.hom g.hom =
      H.source.hom := by
    rw [hsource, Category.assoc, Category.assoc, pullbackSymmetry_hom_comp_snd]
  have hm : mA.hom = eqToHom he ≫ Z.subspace.ι ≫ sym.hom :=
    pullback.hom_ext (hmfst'.trans hzfst.symm) (hmsnd'.trans hzsnd.symm)
  have hmo : Space.IsOpenImmersion C S hS mA.hom := by
    rw [hm]
    exact MorphismProperty.RespectsIso.precomp _ (eqToHom he) _
      (MorphismProperty.RespectsIso.postcomp _ sym.hom Z.subspace.ι Z.isOpen.2)
  have hmonoM : Mono mA.hom :=
    Space.mono_of_isImmersion C S hS (Space.isImmersion_of_isOpenImmersion C S hS hmo)
  have hmonoR : Mono rA.hom := mono_of_mono_fac
    (congrArg (fun k : H.arrows ⟶ AlgebraicSpaces.fiberProduct C S hS G.source g => k.hom)
      hrsnd)
  have hmonoQ : Mono qA.hom := mono_of_mono_fac
    (congrArg (fun k : H.arrows ⟶ restrictionArrows G g => k.hom) hqrA)
  have hl : Space.IsEtale C S hS (fiberProductSnd g G.target).hom :=
    Space.isEtale_of_isPullback C S hS (fiberProductFst g G.target)
      (fiberProductSnd g G.target) g G.target P1 hg
  have hrr : Space.IsEtale C S hS (fiberProductSnd (fiberProductSnd g G.target)
      (fiberProductFst G.source g)).hom :=
    Space.isEtale_of_isPullback C S hS
      (fiberProductFst (fiberProductSnd g G.target) (fiberProductFst G.source g))
      (fiberProductSnd (fiberProductSnd g G.target) (fiberProductFst G.source g))
      (fiberProductSnd g G.target) (fiberProductFst G.source g) P3 hl
  have hre : Space.IsEtale C S hS rA.hom :=
    Space.isEtale_of_isEtale_over C S hS H.arrows.property
      (restrictionArrows G g).property
      (AlgebraicSpaces.fiberProduct C S hS G.source g).property rA.hom mA.hom
      (fiberProductSnd (fiberProductSnd g G.target) (fiberProductFst G.source g)).hom
      (Space.isEtale_of_isOpenImmersion C S hS hmo) hrr
      (congrArg (fun k : H.arrows ⟶ AlgebraicSpaces.fiberProduct C S hS G.source g => k.hom)
        hrsnd)
  have hro := Space.isOpenImmersion_of_isEtale_of_mono C S hS rA.hom H.arrows.property
    (restrictionArrows G g).property hre hmonoR
  have hqopen : Space.IsOpenImmersion C S hS qA.hom := by
    have hcomp : qA.hom = rA.hom ≫ (eqToHom Rst.arrows_eq.symm :
        restrictionArrows G g ⟶ Rst.groupoid.arrows).hom := rfl
    rw [hcomp]
    exact MorphismProperty.RespectsIso.postcomp _ _ rA.hom hro
  have hfin : Space.IsFinite C S hS H.source.hom := by
    rw [hsource]
    simpa only [eqToIso.hom] using
      Space.isFinite_precomp_iso C S hS (eqToIso he) _ Z.finite_projection
  exact @nonempty_openFiniteSubgroupoid_of_embedding C S hS B H Rst.groupoid p qA.hom hmonoQ
    hqs hqt
    (preserves_comp_of_fullyFaithful H.toGroupoidInFunctors
      Rst.groupoid.toGroupoidInFunctors G.toGroupoidInFunctors f Rst.hom.toGroupoidHom
      Rst.evaluation_fullyFaithful p.hom qA.hom hqs hqt hqo hqa) hqopen hfin

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end
