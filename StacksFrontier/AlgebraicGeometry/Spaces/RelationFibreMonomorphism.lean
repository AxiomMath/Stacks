module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.GroupoidOfEquivalenceRelation
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.FiniteFlatQuotientAffine
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.EtaleUniversallyBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteFlatQuotientFromPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.KernelPair
public import StacksFrontier.AlgebraicGeometry.Spaces.PresentationFromQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationFibers
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Subcanonical
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A monomorphic field representative from an étale quasi-compact relation

Conditions (3) and (4) of Stacks 03JU, at a point `x` of an algebraic space `F` over `S`, are
that `x` has a field-valued representative whose two self-intersection projections are étale and
quasi-compact, and that `x` has a field-valued representative presenting it by a monomorphism.
This file proves them equivalent.

The substantial direction is (3) implies (4). Let `f : h_U ⟶ F` be the morphism presented by a
representative as in condition (3), so `U = Spec k` for a field `k`, and let `R = U ×_F U` be its
kernel pair, which exists because the diagonal of `F` is representable. Condition (3) says that
the two projections `R ⟶ U` are étale and quasi-compact, and an étale quasi-compact morphism to
the spectrum of a field is finite locally free with affine source. So `(U, R)` is a finite locally
free equivalence relation on an affine scheme, and Stacks 03BM represents its fppf quotient sheaf
by the spectrum of the ring of invariant functions — a subring of `k`, hence a domain, whose
spectrum receives a surjection from the one-point space `Spec k` and is therefore itself a field.
The quotient sheaf also receives a monomorphism to `F`, because `R` is the kernel pair of `f` and
`F` is a sheaf, so composing gives the monomorphism from the spectrum of a field that condition
(4) asks for.

Nothing here uses Stacks 03DZ, which is how the source routes this step: 03DZ derives the same
representation from quasi-separatedness of the quotient, and quasi-separatedness is only used to
make the relation quasi-compact — which condition (3) grants outright.

## Main definitions

No new definitions are introduced; the four conditions are the ones of
`StacksFrontier.AlgebraicGeometry.Spaces.RelationFibers`.

## Main results

All three live in the namespace `AlgebraicGeometry.Space`, whose prefix is dropped here.

* `HasEtaleQuasiCompactFieldRepresentative.hasMonomorphicFieldRepresentative`:
  **Stacks 03JU, part (3) implies part (4).**
* `HasMonomorphicFieldRepresentative.hasEtaleQuasiCompactFieldRepresentative`:
  **Stacks 03JU, part (4) implies part (3)**, which is formal: a monomorphism has invertible
  self-intersection projections.
* `hasEtaleQuasiCompactFieldRepresentative_iff`: the two conditions are equivalent.

## Implementation notes

**The quotient is taken as a groupoid scheme.** Stacks 03BM is stated in this development for a
`Stacks.Groupoids.GroupoidScheme`, while the relation of a chart is a
`Stacks.Groupoids.PreRelation`. The canonical groupoid extending an equivalence relation,
`AlgebraicGeometry.groupoidSchemeOfIsEquivalenceRelation`, has the prescribed objects, arrows,
source and target only up to the propositional equalities of
`AlgebraicGeometry.ExtendsRelation`, so the whole 03BM step is packaged in one private lemma
which takes the groupoid scheme and the `ExtendsRelation` datum as inputs and substitutes the
two object equalities away at the start. That is what keeps the transport out of the main proof.

**Why the invariant ring is a field.** `AlgebraicGeometry.invariantRing` of the groupoid is a
subring of the global functions on `Spec k`, hence a domain; the canonical morphism out of
`Spec k` is surjective on points by Tag 03BM, so the spectrum of the invariant ring is a
subsingleton. A domain with at most one prime ideal is a field, since a non-unit would generate a
proper ideal contained in a maximal — hence prime — ideal other than `(0)`.

**Where the monomorphism comes from.** The descent of `f` along the projection to the quotient
sheaf is a monomorphism already at the level of the quotient *presheaf*, because `R` is the kernel
pair of `f`; sheafification of a monomorphism into a sheaf stays a monomorphism, since the lift
factors as the sheafification of the map followed by the inverse of the sheafification unit of
`F`. No local surjectivity argument is needed for this half.

**What is not here.** Condition (2) of Stacks 03JU implies condition (3) — the step that produces
an étale quasi-compact relation from finiteness of the relation fibres — is not proved in this
repository, so neither is the composite (2) implies (4) that
`AlgebraicGeometry.Space.exists_mono_isFinite_fieldFibre_of_finiteFibres` carries as its
hypothesis `h03JU`.

## References

* [Stacks Project, Tag 03JU](https://stacks.math.columbia.edu/tag/03JU)
* [Stacks Project, Tag 03BM](https://stacks.math.columbia.edu/tag/03BM)
* [Stacks Project, Tag 0262](https://stacks.math.columbia.edu/tag/0262)
* [Stacks Project, Tag 02VG](https://stacks.math.columbia.edu/tag/02VG)
* [Stacks Project, Tag 02GL](https://stacks.math.columbia.edu/tag/02GL)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Groupoids Stacks.Morphisms

universe u v w

namespace AlgebraicGeometry.Space

/-! ### General facts -/

/-- The map out of the coequalizer of a kernel pair of presheaves of types is a monomorphism:
two sections with the same image lift, section-wise, to a point of the relation, and the
coequalizer identifies the two legs of that point. -/
private lemma mono_coequalizerDesc_of_isPullback {C : Type v} [Category.{w} C]
    {R U X : Cᵒᵖ ⥤ Type u} (s t : R ⟶ U) (f : U ⟶ X)
    (h : IsPullback s t f f) : Mono (coequalizer.desc f h.w) := by
  refine (NatTrans.mono_iff_mono_app _).2 fun A ↦
    (CategoryTheory.mono_iff_injective _).2 fun x y hxy ↦ ?_
  have surj := (CategoryTheory.epi_iff_surjective ((coequalizer.π s t).app A)).1 inferInstance
  obtain ⟨a, rfl⟩ := surj x
  obtain ⟨b, rfl⟩ := surj y
  have hab : f.app A a = f.app A b := by
    simpa only [← NatTrans.comp_app_apply, coequalizer.π_desc] using hxy
  obtain ⟨r, hr, hr'⟩ := Types.exists_of_isPullback
    (h.map ((evaluation _ _).obj A)) a b hab
  rw [← hr, ← hr']
  exact congrFun (congrArg (fun k ↦ (k.app A).hom) (coequalizer.condition s t)) r

/-- The sheafification lift of a monomorphism into a sheaf is a monomorphism: it factors as the
sheafification of the map followed by the inverse of the sheafification unit of the target. -/
private lemma mono_sheafifyLift {C : Type v} [Category.{w} C]
    (J : GrothendieckTopology C) [HasSheafify J (Type u)]
    {G X : Cᵒᵖ ⥤ Type u} (f : G ⟶ X) [Mono f]
    (hX : Presheaf.IsSheaf J X) : Mono (sheafifyLift J f hX) := by
  have : IsIso (toSheafify J X) := isIso_toSheafify J hX
  have he : sheafifyLift J f hX = sheafifyMap J f ≫ inv (toSheafify J X) := by
    apply sheafify_hom_ext J (hQ := hX)
    rw [toSheafify_sheafifyLift, ← Category.assoc, ← toSheafify_naturality]
    simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [he]
  infer_instance

/-! ### The quotient of an affine field relation -/

/-- **The fppf quotient sheaf of a finite locally free equivalence relation on the spectrum of a
field is represented by the spectrum of a field in the same big fppf site.** This is Stacks 03BM,
together with the size bound `AlgebraicGeometry.contains_quotientOver` and
`AlgebraicGeometry.Space.isField_invariantRing`, transported from the canonical groupoid scheme
extending the relation onto the relation itself.

The groupoid scheme and the `AlgebraicGeometry.ExtendsRelation` datum are inputs rather than
being built here, so that the two object equalities they carry can be substituted away; with
`AlgebraicGeometry.groupoidSchemeOfIsEquivalenceRelation` inlined they could not be, since the
groupoid would then depend on the objects being substituted. -/
private theorem exists_field_quotient_of_extendsRelation
    {S : Scheme.{u}} {R U : Over S} (j : PreRelation R U)
    (G : GroupoidScheme S) (hG : ExtendsRelation j G)
    (hequiv : IsEquivalenceRelation j.target j.source)
    (haU : IsAffine U.left) (haR : IsAffine R.left)
    (hsf : IsFiniteLocallyFree j.source.left) (htf : IsFiniteLocallyFree j.target.left)
    (hdom : IsDomain Γ(U.left, ⊤)) (hsub : Subsingleton ↥U.left)
    (B : BigFppfSite.{u}) (hS : B.Contains S) (hcU : B.Contains U.left)
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)] :
    ∃ (k' : Type u) (_ : Field k') (_ : B.Contains (Spec (CommRingCat.of k')))
      (b' : Spec (CommRingCat.of k') ⟶ S) (q : U ⟶ Over.mk b'),
      ∃ hMs : Presheaf.IsSheaf (BigFppfOver.topology B S hS)
          (Stacks.Groupoids.points (Over.post (X := B.obj hS) B.inclusion) (Over.mk b')),
        ∃ w : quotientSheaf (BigFppfOver.topology B S hS)
              (Over.post (X := B.obj hS) B.inclusion) j ⟶
            ⟨Stacks.Groupoids.points (Over.post (X := B.obj hS) B.inclusion) (Over.mk b'),
              hMs⟩,
          IsIso w ∧
            toQuotientSheaf (BigFppfOver.topology B S hS)
                (Over.post (X := B.obj hS) B.inclusion) j ≫ w.hom =
              (Over.post (X := B.obj hS) B.inclusion).op.whiskerLeft (yoneda.map q) := by
  obtain ⟨hobj, harr, hsrc, htgt⟩ := hG
  subst hobj
  subst harr
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hsrc htgt
  have _ : IsAffine G.objects.left := haU
  have _ : IsAffine G.arrows.left := haR
  have _ : IsFiniteLocallyFree G.source.left := hsrc ▸ hsf
  have _ : IsFiniteLocallyFree G.target.left := htgt ▸ htf
  have _ : IsEquivalenceRelation G.target G.source := by rwa [hsrc, htgt]
  have hj : prod.lift G.target G.source = j := by
    rw [hsrc, htgt, ← prod.comp_lift, prod.lift_fst_snd, Category.comp_id]
  have hrep := quotientSheaf_isRepresented_of_isPullback G (quotientProjection G)
    (affineFiniteFlatQuotient G).finiteLocallyFree (affineFiniteFlatQuotient G).surjective
    (affineFiniteFlatQuotient G).kernelPair B hS
  refine ⟨invariantRing G, (isField_invariantRing G hdom hsub).toField,
    contains_quotientOver G B hcU, (quotientBaseMap G).val, quotientProjection G, ?_⟩
  rwa [← hj]

/-! ### Étale quasi-compact morphisms to the spectrum of a field -/

/-- An étale quasi-compact morphism to the spectrum of a field is finite locally free, and its
source is affine. It is locally quasi-finite because it is étale, hence finite because the
spectrum of a field is locally Artinian, and étale supplies flatness and finite presentation. -/
@[ega "IV 18.2.7" "special case"]
private theorem isFiniteLocallyFree_and_isAffine_of_etale_quasiCompact_field
    (k : Type u) [Field k] {Z : Scheme.{u}} (g : Z ⟶ Spec (CommRingCat.of k))
    [Etale g] [QuasiCompact g] : IsFiniteLocallyFree g ∧ IsAffine Z := by
  have _ : LocallyQuasiFinite g := (locallyQuasiFinite_of_etale g).2
  have _ : _root_.AlgebraicGeometry.IsFinite g := IsFinite.of_locallyQuasiFinite g
  exact ⟨(isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation g).2
    ⟨inferInstance, inferInstance, inferInstance⟩, isAffine_of_isAffineHom g⟩

/-! ### The monomorphic descent of a chart along its own relation -/

/-- **The quotient sheaf of the kernel pair of a chart receives a monomorphism to the target.**
For a morphism `f : h_U ⟶ F` of presheaves on the big fppf site of `S` with `F` a sheaf, and a
pair `s, t : R ⟶ U` exhibiting `R` as the kernel pair of `f`, the descent of `f` to the quotient
sheaf of `R` is a monomorphism, and it recovers `f` on `h_U`. -/
private theorem exists_mono_quotientSheafDesc (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hFsh : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    {R U : BigFppfOver B S hS} (f : yoneda.obj U ⟶ F) (s t : R ⟶ U)
    (hR : IsPullback (yoneda.map s) (yoneda.map t) f f) :
    ∃ d : quotientSheaf (BigFppfOver.topology B S hS)
        (Over.post (X := B.obj hS) B.inclusion) (relation B S hS s t) ⟶
        (⟨F, hFsh⟩ : Sheaf (BigFppfOver.topology B S hS) (Type u)),
      Mono d.hom ∧
      toQuotientSheaf (BigFppfOver.topology B S hS)
          (Over.post (X := B.obj hS) B.inclusion) (relation B S hS s t) ≫ d.hom =
        ((Over.post (X := B.obj hS) B.inclusion).yonedaMapIso U).inv ≫ f := by
  let J := BigFppfOver.topology B S hS
  let G : BigFppfOver B S hS ⥤ Over S := Over.post B.inclusion
  let j := relation B S hS s t
  let _ : G.Full := by
    show (Over.post (X := B.obj hS) B.inclusion).Full
    infer_instance
  let _ : G.Faithful := by
    show (Over.post (X := B.obj hS) B.inclusion).Faithful
    infer_instance
  let eU := G.yonedaMapIso U
  let eR := G.yonedaMapIso R
  let k : Stacks.Groupoids.points G (G.obj U) ⟶ F := eU.inv ≫ f
  have hs : yoneda.map s ≫ eU.hom = eR.hom ≫ Stacks.Groupoids.sourceMap G j := by
    ext A a
    show G.map (a ≫ s) ≫ 𝟙 _ =
      (G.map a ≫ 𝟙 _) ≫ (prod.lift (G.map t) (G.map s) ≫ prod.snd)
    simp
  have ht : yoneda.map t ≫ eU.hom = eR.hom ≫ Stacks.Groupoids.targetMap G j := by
    ext A a
    show G.map (a ≫ t) ≫ 𝟙 _ =
      (G.map a ≫ 𝟙 _) ≫ (prod.lift (G.map t) (G.map s) ≫ prod.fst)
    simp
  have hk : IsPullback (Stacks.Groupoids.sourceMap G j) (Stacks.Groupoids.targetMap G j) k k :=
    hR.of_iso eR eU eU (Iso.refl F) hs ht (by simp [k]) (by simp [k])
  refine ⟨quotientSheafDesc J G j ⟨F, hFsh⟩ k hk.w, ?_, ?_⟩
  · have _ : Mono (coequalizer.desc k hk.w) :=
      mono_coequalizerDesc_of_isPullback _ _ k hk
    exact mono_sheafifyLift J (coequalizer.desc k hk.w) hFsh
  · exact toQuotientSheaf_quotientSheafDesc J G j ⟨F, hFsh⟩ k hk.w

/-! ### Stacks 03JU, conditions (3) and (4) -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- A scheme property tested after representable base change on the two projections of a
represented kernel pair holds for the two projections themselves. -/
private theorem kernelPair_property (P : MorphismProperty Scheme.{u})
    {U R : BigFppfOver B S hS} (f : yoneda.obj U ⟶ F) (s t : R ⟶ U)
    (hR : IsPullback (yoneda.map s) (yoneda.map t) f f)
    (hfst : (MorphismProperty.presheaf (MorphismProperty.inverseImage P
      (BigFppfOver.toScheme B S hS))) (pullback.fst f f))
    (hsnd : (MorphismProperty.presheaf (MorphismProperty.inverseImage P
      (BigFppfOver.toScheme B S hS))) (pullback.snd f f)) :
    P ((BigFppfOver.toScheme B S hS).map s) ∧ P ((BigFppfOver.toScheme B S hS).map t) := by
  let e := hR.isoIsPullback (yoneda.obj U) (yoneda.obj U) (IsPullback.of_hasPullback f f)
  constructor
  · refine hfst.property (𝟙 (yoneda.obj U)) e.hom s (IsPullback.of_horiz_isIso ⟨?_⟩)
    simpa using (by simp [e] : e.hom ≫ pullback.fst f f = yoneda.map s)
  · refine hsnd.property (𝟙 (yoneda.obj U)) e.hom t (IsPullback.of_horiz_isIso ⟨?_⟩)
    simpa using (by simp [e] : e.hom ≫ pullback.snd f f = yoneda.map t)

private theorem exists_field_quotient_of_kernelPair
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)] (p : FieldValuedPoint B S hS F)
    {R : BigFppfOver B S hS} (s t : R ⟶ p.siteObject)
    (hR : IsPullback (yoneda.map s) (yoneda.map t) (fieldMorphism B S hS F p)
      (fieldMorphism B S hS F p))
    [Etale ((BigFppfOver.toScheme B S hS).map s)]
    [QuasiCompact ((BigFppfOver.toScheme B S hS).map s)]
    [Etale ((BigFppfOver.toScheme B S hS).map t)]
    [QuasiCompact ((BigFppfOver.toScheme B S hS).map t)] :
    ∃ (k' : Type u) (_ : Field k') (_ : B.Contains (Spec (CommRingCat.of k')))
      (b' : Spec (CommRingCat.of k') ⟶ S)
      (q : (Over.post (X := B.obj hS) B.inclusion).obj p.siteObject ⟶ Over.mk b'),
      ∃ hMs : Presheaf.IsSheaf (BigFppfOver.topology B S hS)
          (Stacks.Groupoids.points (Over.post (X := B.obj hS) B.inclusion) (Over.mk b')),
        ∃ w : quotientSheaf (BigFppfOver.topology B S hS)
              (Over.post (X := B.obj hS) B.inclusion) (relation B S hS s t) ⟶
            ⟨Stacks.Groupoids.points (Over.post (X := B.obj hS) B.inclusion) (Over.mk b'),
              hMs⟩,
          IsIso w ∧
            toQuotientSheaf (BigFppfOver.topology B S hS)
                (Over.post (X := B.obj hS) B.inclusion) (relation B S hS s t) ≫ w.hom =
              (Over.post (X := B.obj hS) B.inclusion).op.whiskerLeft (yoneda.map q) := by
  let U : BigFppfOver B S hS := p.siteObject
  obtain ⟨hflfs, haffR⟩ := isFiniteLocallyFree_and_isAffine_of_etale_quasiCompact_field
    p.carrier ((BigFppfOver.toScheme B S hS).map s)
  obtain ⟨hflft, -⟩ := isFiniteLocallyFree_and_isAffine_of_etale_quasiCompact_field
    p.carrier ((BigFppfOver.toScheme B S hS).map t)
  have hrt : (relation B S hS s t).target = (Over.post (X := B.obj hS) B.inclusion).map t :=
    prod.lift_fst _ _
  have hrs : (relation B S hS s t).source = (Over.post (X := B.obj hS) B.inclusion).map s :=
    prod.lift_snd _ _
  have hequiv : IsEquivalenceRelation (relation B S hS s t).target
      (relation B S hS s t).source := by
    rw [hrt, hrs]
    exact isEquivalenceRelation_of_isPullback B S hS _ t s hR.flip
  have haU : IsAffine ((Over.post (X := B.obj hS) B.inclusion).obj U).left := by
    show IsAffine (Spec (CommRingCat.of p.carrier))
    infer_instance
  have hsf : IsFiniteLocallyFree (relation B S hS s t).source.left := by rwa [hrs]
  have htf : IsFiniteLocallyFree (relation B S hS s t).target.left := by rwa [hrt]
  have hdom : IsDomain Γ(((Over.post (X := B.obj hS) B.inclusion).obj U).left, ⊤) := by
    show IsDomain Γ(Spec (CommRingCat.of p.carrier), ⊤)
    exact (Scheme.ΓSpecIso (CommRingCat.of p.carrier)).commRingCatIsoToRingEquiv.toMulEquiv.isDomain
      p.carrier
  have hsub : Subsingleton ↥((Over.post (X := B.obj hS) B.inclusion).obj U).left := by
    show Subsingleton ↥(Spec (CommRingCat.of p.carrier))
    infer_instance
  exact exists_field_quotient_of_extendsRelation (relation B S hS s t)
    (groupoidSchemeOfIsEquivalenceRelation (relation B S hS s t))
    (groupoidSchemeOfIsEquivalenceRelation_extendsRelation _)
    hequiv haU haffR hsf htf hdom hsub B hS p.contained

private theorem hasMonomorphicFieldRepresentative_of_mono_comp {x : points B S hS F}
    (p : FieldValuedPoint B S hS F) (hpx : p.class B S hS F = x) {k' : Type u} [Field k']
    (hk' : B.Contains (Spec (CommRingCat.of k'))) (b' : Spec (CommRingCat.of k') ⟶ S)
    (m : p.siteObject ⟶ (Over.mk (⟨b'⟩ : B.obj hk' ⟶ B.obj hS) : BigFppfOver B S hS))
    (g : yoneda.obj (Over.mk (⟨b'⟩ : B.obj hk' ⟶ B.obj hS) : BigFppfOver B S hS) ⟶ F)
    [Mono g] (hg : yoneda.map m ≫ g = fieldMorphism B S hS F p) :
    HasMonomorphicFieldRepresentative B S hS F x := by
  let p' : FieldValuedPoint B S hS F :=
    { carrier := k', field := inferInstance, contained := hk', toBase := b',
      value := yonedaEquiv g }
  have hfm : fieldMorphism B S hS F p' = g := Equiv.symm_apply_apply _ _
  have hdom : FieldValuedPoint.Dominates B S hS F p p' := by
    refine ⟨m, ?_⟩
    show F.map m.op (yonedaEquiv g) = p.value
    rw [yonedaEquiv_naturality g m, hg]
    exact yonedaEquiv_fieldMorphism B S hS F p
  have hclass : p.class B S hS F = p'.class B S hS F :=
    Quot.sound ⟨p, FieldValuedPoint.dominates_refl B S hS F p, hdom⟩
  refine ⟨p', hclass.symm.trans hpx, ?_⟩
  rw [hfm]
  infer_instance

private theorem hasMonomorphicFieldRepresentative_of_quotient
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    (hFsh : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F) {x : points B S hS F}
    (p : FieldValuedPoint B S hS F) (hpx : p.class B S hS F = x)
    {R : BigFppfOver B S hS} (s t : R ⟶ p.siteObject)
    (hR : IsPullback (yoneda.map s) (yoneda.map t) (fieldMorphism B S hS F p)
      (fieldMorphism B S hS F p))
    {k' : Type u} [Field k'] (hk' : B.Contains (Spec (CommRingCat.of k')))
    (b' : Spec (CommRingCat.of k') ⟶ S)
    (q : (Over.post (X := B.obj hS) B.inclusion).obj p.siteObject ⟶ Over.mk b')
    (hMs : Presheaf.IsSheaf (BigFppfOver.topology B S hS)
      (Stacks.Groupoids.points (Over.post (X := B.obj hS) B.inclusion) (Over.mk b')))
    (w : quotientSheaf (BigFppfOver.topology B S hS)
        (Over.post (X := B.obj hS) B.inclusion) (relation B S hS s t) ⟶
      ⟨Stacks.Groupoids.points (Over.post (X := B.obj hS) B.inclusion) (Over.mk b'), hMs⟩)
    [IsIso w]
    (hfac : toQuotientSheaf (BigFppfOver.topology B S hS)
        (Over.post (X := B.obj hS) B.inclusion) (relation B S hS s t) ≫ w.hom =
      (Over.post (X := B.obj hS) B.inclusion).op.whiskerLeft (yoneda.map q)) :
    HasMonomorphicFieldRepresentative B S hS F x := by
  let f : yoneda.obj p.siteObject ⟶ F := fieldMorphism B S hS F p
  let U : BigFppfOver B S hS := p.siteObject
  obtain ⟨d, _, hdfac⟩ := exists_mono_quotientSheafDesc B S hS hFsh f s t hR
  let U' : BigFppfOver B S hS := Over.mk (⟨b'⟩ : B.obj hk' ⟶ B.obj hS)
  let G : BigFppfOver B S hS ⥤ Over S := Over.post B.inclusion
  let _ : G.Full := by
    show (Over.post (X := B.obj hS) B.inclusion).Full
    infer_instance
  let _ : G.Faithful := by
    show (Over.post (X := B.obj hS) B.inclusion).Faithful
    infer_instance
  let eU : yoneda.obj U ≅ Stacks.Groupoids.points G (G.obj U) := G.yonedaMapIso U
  let eU' : yoneda.obj U' ≅ Stacks.Groupoids.points G (Over.mk b') := G.yonedaMapIso U'
  let gpre : yoneda.obj U' ⟶ F := eU'.hom ≫ inv w.hom ≫ d.hom
  have _ : Mono gpre := by
    show Mono (eU'.hom ≫ inv w.hom ≫ d.hom)
    infer_instance
  let m : U ⟶ U' := G.preimage (show G.obj U ⟶ G.obj U' from q)
  have hm : G.map m = q := G.map_preimage (show G.obj U ⟶ G.obj U' from q)
  have h1 : yoneda.map m ≫ eU'.hom = eU.hom ≫
      (Over.post (X := B.obj hS) B.inclusion).op.whiskerLeft (yoneda.map q) := by
    ext A a
    show G.map (a ≫ m) = G.map a ≫ q
    rw [G.map_comp, hm]
    rfl
  refine hasMonomorphicFieldRepresentative_of_mono_comp B S hS F p hpx hk' b' m gpre ?_
  calc yoneda.map m ≫ gpre
      = (yoneda.map m ≫ eU'.hom) ≫ inv w.hom ≫ d.hom := by
        simp only [gpre, Category.assoc]
    _ = eU.hom ≫ (toQuotientSheaf (BigFppfOver.topology B S hS)
          (Over.post (X := B.obj hS) B.inclusion) (relation B S hS s t) ≫ w.hom) ≫
            inv w.hom ≫ d.hom := by
        rw [h1, hfac]
        simp only [Category.assoc]
    _ = eU.hom ≫ toQuotientSheaf (BigFppfOver.topology B S hS)
          (Over.post (X := B.obj hS) B.inclusion) (relation B S hS s t) ≫ d.hom := by
        simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    _ = f := by
        rw [hdfac]
        exact Iso.hom_inv_id_assoc eU f

/-- **Stacks 03JU, part (3) implies part (4).** If a point `x` of an algebraic space `F` over `S`
has a field-valued representative whose two self-intersection projections are étale and
quasi-compact, then `x` has a field-valued representative presenting it by a monomorphism.

Let `f : h_U ⟶ F` be the morphism presented by the representative of condition (3), so that `U`
is `Spec k` for a field `k`, and let `R` be the kernel pair of `f`, which exists because the
diagonal of `F` is representable. The two projections `R ⟶ U` are étale and quasi-compact, hence
finite locally free with `R` affine, so `(U, R)` is a finite locally free equivalence relation on
an affine scheme; Stacks 03BM represents its fppf quotient sheaf by the spectrum of the invariant
ring, which is a field, and which lies in the site because the quotient does not increase size.
The descent of `f` to that quotient sheaf is a monomorphism because `R` is the kernel pair of `f`
and `F` is a sheaf, and the resulting field-valued point is dominated by the original one, so it
represents the same point of `|F|`. -/
@[stacks 03JU "part (3) implies part (4)"]
theorem HasEtaleQuasiCompactFieldRepresentative.hasMonomorphicFieldRepresentative
    (hF : IsAlgebraicSpace B S hS F) {x : points B S hS F}
    (h : HasEtaleQuasiCompactFieldRepresentative B S hS F x) :
    HasMonomorphicFieldRepresentative B S hS F x := by
  classical
  obtain ⟨p, hpx, hfst, hsnd⟩ := h
  have _ : HasSheafify (BigFppfOver.topology B S hS) (Type u) :=
    BigFppfOver.hasSheafify_type B S hS
  let f : yoneda.obj p.siteObject ⟶ F := fieldMorphism B S hS F p
  have hq := hF.diagonal_representable.of_diag f
  let R : BigFppfOver B S hS := hq.pullback f
  let s : R ⟶ p.siteObject := yoneda.preimage (hq.fst f)
  let t : R ⟶ p.siteObject := hq.snd f
  have hR : IsPullback (yoneda.map s) (yoneda.map t) f f := by
    simpa [s, t] using hq.isPullback f
  obtain ⟨hPs, hPt⟩ := kernelPair_property B S hS F
    ((@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) ⊓
      (@AlgebraicGeometry.QuasiCompact.{u} : MorphismProperty Scheme.{u})) f s t hR hfst hsnd
  have _ : Etale ((BigFppfOver.toScheme B S hS).map s) := hPs.1
  have _ : QuasiCompact ((BigFppfOver.toScheme B S hS).map s) := hPs.2
  have _ : Etale ((BigFppfOver.toScheme B S hS).map t) := hPt.1
  have _ : QuasiCompact ((BigFppfOver.toScheme B S hS).map t) := hPt.2
  obtain ⟨k', _, hk', b', q, hMs, w, _, hfac⟩ :=
    exists_field_quotient_of_kernelPair B S hS F p s t hR
  exact hasMonomorphicFieldRepresentative_of_quotient B S hS F hF.isSheaf p hpx s t hR hk' b' q
    hMs w hfac

/-- An isomorphism of presheaves is étale and quasi-compact after every representable base
change: the base change along any morphism out of a representable is an isomorphism, which a
fully faithful embedding reflects to an isomorphism of objects of the site. -/
private theorem etaleQuasiCompact_of_isIso {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (g : X ⟶ Y) [IsIso g] :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      ((@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) ⊓
        (@AlgebraicGeometry.QuasiCompact.{u} : MorphismProperty Scheme.{u}))
      (BigFppfOver.toScheme B S hS))) g := by
  refine ⟨Functor.relativelyRepresentable.of_isIso yoneda g, ?_⟩
  intro a b g' fst snd hsq
  have _ : IsIso (yoneda.map snd) := hsq.isIso_snd_of_isIso (by infer_instance)
  have _ : IsIso snd := Yoneda.isIso snd
  exact ⟨inferInstance, inferInstance⟩

/-- **Stacks 03JU, part (4) implies part (3).** A field-valued representative presenting a point
by a monomorphism has invertible self-intersection projections, and an isomorphism is étale and
quasi-compact after every representable base change. -/
@[stacks 03JU "part (4) implies part (3)"]
theorem HasMonomorphicFieldRepresentative.hasEtaleQuasiCompactFieldRepresentative
    {x : points B S hS F} (h : HasMonomorphicFieldRepresentative B S hS F x) :
    HasEtaleQuasiCompactFieldRepresentative B S hS F x := by
  obtain ⟨p, hpx, hmono⟩ := h
  have _ : Mono (fieldMorphism B S hS F p) := hmono
  exact ⟨p, hpx, etaleQuasiCompact_of_isIso B S hS _, etaleQuasiCompact_of_isIso B S hS _⟩

/-- **Stacks 03JU, conditions (3) and (4) are equivalent.** A point of an algebraic space over
`S` has a field-valued representative with étale quasi-compact self-intersection projections
exactly when it has a field-valued representative presenting it by a monomorphism. -/
theorem hasEtaleQuasiCompactFieldRepresentative_iff (hF : IsAlgebraicSpace B S hS F)
    (x : points B S hS F) :
    HasEtaleQuasiCompactFieldRepresentative B S hS F x ↔
      HasMonomorphicFieldRepresentative B S hS F x :=
  ⟨HasEtaleQuasiCompactFieldRepresentative.hasMonomorphicFieldRepresentative B S hS F hF,
    HasMonomorphicFieldRepresentative.hasEtaleQuasiCompactFieldRepresentative B S hS F⟩

end AlgebraicGeometry.Space

end
