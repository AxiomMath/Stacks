module

public import Mathlib.RingTheory.Etale.Field
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleQuasiFinite
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.GroupoidOfEquivalenceRelation
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.FiniteFlatQuotientAffine
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.OverField
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteFlatQuotientFromPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.KernelPair
public import StacksFrontier.AlgebraicGeometry.Spaces.PresentationFromQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A quasi-separated algebraic space with a field atlas is the spectrum of a field

Stacks 03DZ: an algebraic space `X` over a scheme `S` which admits a surjective étale morphism
`Spec(k) ⟶ X` from the spectrum of a field, and which is quasi-separated, is isomorphic to
`Spec(k')` for a subfield `k' ⊂ k` with `k/k'` finite separable.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.exists_field_spectrum_of_surjective_etale` is the lemma, with
  quasi-separatedness read as in Stacks 03BS part (3): the representing field, the finite
  separable extension, the compatibility of the two structure morphisms over `S`, and the
  identification of the given atlas with the morphism induced by the field extension.
* `AlgebraicGeometry.Space.exists_field_spectrum_of_surjective_etale_of_isQuasiSeparatedOver`
  is the same conclusion from the weaker hypothesis of quasi-separatedness over `S`, which is
  what the proof consumes.
* `AlgebraicGeometry.Space.isQuasiSeparatedOver_of_isAbsolutelyQuasiSeparated` connects the
  two hypotheses. It is proved in
  `StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/SeparationAxioms.lean`, which this file
  imports, alongside the rest of Stacks 04ZI.

## Implementation notes

**The shape of the proof.** Write `R = Spec(k) ×_X Spec(k)` for the kernel pair of the atlas
`f`, which exists because the diagonal of `X` is representable. Both projections `R ⟶ Spec(k)`
are étale, being base changes of `f`. Quasi-separatedness enters exactly once: the comparison
`R ⟶ Spec(k) ×_S Spec(k)` is a base change of the diagonal of `X`, hence quasi-compact, and
`Spec(k) ×_S Spec(k) ⟶ Spec(k)` is a base change of the structure morphism `Spec(k) ⟶ S`, which
is quasi-compact because its source is a single point. So both projections of `R` are étale and
quasi-compact over the spectrum of a field, therefore finite locally free with affine source
(an étale morphism is locally quasi-finite, and the spectrum of a field is locally Artinian).
Stacks 03BM then represents the fppf quotient sheaf of the relation by the spectrum of the ring
of invariant functions, a subring of the global functions on `Spec(k)`, hence a domain; the
canonical map out of `Spec(k)` is surjective on points, so that spectrum has at most one point
and the invariant ring is a field. Finally Stacks 0262 part (3) identifies `X` itself with that
quotient sheaf, because `f` is a surjective étale atlas. Separability of `k` over the invariant
field is read off the composite: the atlas becomes the morphism of affine schemes induced by
the field extension, and it is étale, so the extension is formally étale and of finite
presentation, hence finite and separable.

**Two readings of quasi-separatedness, and why both appear.** Stacks 03BS part (3) defines a
quasi-separated algebraic space over `S` as one which is quasi-separated after being viewed
over `Spec(ℤ)`, which is `AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated`; the source's
proof of 03DZ, however, consumes only quasi-separatedness over `S` itself — its displayed fibre
square for `R` is taken over `X ×_S X` — which is
`AlgebraicGeometry.Space.IsQuasiSeparatedOver`, Stacks 02X5. The latter is the weaker
hypothesis, so the proof is run with it and the carded form is deduced. The deduction is
`AlgebraicGeometry.Space.isQuasiSeparatedOver_of_isAbsolutelyQuasiSeparated`: a morphism out of
a presheaf quasi-separated over the terminal scheme has quasi-compact relative diagonal, and
that property descends along the relocalization of Stacks 03I4 part (3) because the relative
diagonal of an algebraic space is representable. It is the converse half of the argument in
`AlgebraicGeometry.Space.isQuasiSeparated_pullbackSnd_iff_isAbsolutelyQuasiSeparated`, taken at
the terminal presheaf instead of at an affine test object, and it belongs with that family
rather than here.

**Why the proof is split in three.** `AlgebraicGeometry.Space.quotientRepresentation` runs the
Stacks 03BM step, which needs the canonical groupoid scheme extending the relation; that
groupoid has the prescribed objects and arrows only up to the propositional equalities of
`AlgebraicGeometry.ExtendsRelation`, so the groupoid and the datum are inputs rather than being
built inside, which is what lets the two object equalities be substituted away at the start.
`AlgebraicGeometry.Space.isIso_quotientSheafDesc` runs the Stacks 0262 part (3) step, comparing
two descriptions of the quotient: the universal property of
`Stacks.Groupoids.quotientSheaf` in the form
`Stacks.Groupoids.quotientSheafDesc` together with
`Stacks.Groupoids.quotientSheafDesc_unique`, and the coequalizer property of the atlas. No
monomorphism or local-surjectivity argument is needed for this: the two universal properties
determine mutually inverse maps. `AlgebraicGeometry.Space.pointLikeCore` assembles those with
the quasi-compactness argument for an atlas whose underlying scheme is affine, locally
Artinian and a single point with a domain of functions, which is the generality the proof
actually uses; the field case is the specialization.

**Two spelling constraints, and why the statements look the way they do.** Three definitionally
equal but syntactically distinct expressions for the scheme underlying the atlas are in play —
`CategoryTheory.Over.post` of the site inclusion applied to it and projected,
`AlgebraicGeometry.BigFppfOver.toScheme` applied to it, and, once the atlas is the concrete
`Spec` of a field, that `Spec` itself. Rewriting tactics match syntactically, so the private
statements are written consistently in the first of these, which is the one Stacks 03BM's
output carries. Two consequences. First,
`AlgebraicGeometry.Space.quotientRepresentation` states the representing object as
`CategoryTheory.Over.post` of an object of the site rather than as a slice object built from
the descended structure morphism, so that it composes with the comparison isomorphism of
`AlgebraicGeometry.Space.yonedaMapIso_naturality` without an intervening transport. Second, the
public statement does not name the ring of invariant functions at all: the atlas scheme there
*is* a concrete `Spec`, which reduces, and the `CommRingCat` wrapper around its global sections
is lost when it does. Instead the morphism out of the atlas is turned back into `Spec` of a ring
map by `AlgebraicGeometry.Spec.map_surjective`, and the algebra structure on `k` is read off
that ring map; the field of invariants survives only as the carrier type.

## References

* [Stacks Project, Tag 0262](https://stacks.math.columbia.edu/tag/0262)
* [Stacks Project, Tag 02GL](https://stacks.math.columbia.edu/tag/02GL)
* [Stacks Project, Tag 02X5](https://stacks.math.columbia.edu/tag/02X5)
* [Stacks Project, Tag 03BM](https://stacks.math.columbia.edu/tag/03BM)
* [Stacks Project, Tag 03BS](https://stacks.math.columbia.edu/tag/03BS)
* [Stacks Project, Tag 03DZ](https://stacks.math.columbia.edu/tag/03DZ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Groupoids Stacks.Morphisms
open Stacks.Spaces

universe u

namespace AlgebraicGeometry.Space

/-! ### General facts -/

/-- An étale quasi-compact morphism to an affine locally Artinian scheme is finite locally
free, and its source is affine. It is locally quasi-finite because it is étale, hence finite
because the target is locally Artinian, and étale supplies flatness and finite presentation. -/
@[ega "IV 18.2.7" "special case"]
private theorem isFiniteLocallyFree_of_etale_quasiCompact {Y Z : Scheme.{u}} [IsAffine Y]
    [IsLocallyArtinian Y] (g : Z ⟶ Y) [Etale g] [QuasiCompact g] :
    IsFiniteLocallyFree g ∧ IsAffine Z := by
  have _ : LocallyQuasiFinite g := (locallyQuasiFinite_of_etale g).2
  have hfin : _root_.AlgebraicGeometry.IsFinite g := IsFinite.of_locallyQuasiFinite g
  exact ⟨(isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation g).2
    ⟨hfin, inferInstance, inferInstance⟩, isAffine_of_isAffineHom g⟩

/-- Naturality of the comparison identifying a representable presheaf on the big fppf site of
`S` with the restriction of a representable presheaf on schemes over `S`. -/
private theorem yonedaMapIso_naturality (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Y : BigFppfOver B S hS} (m : X ⟶ Y) :
    yoneda.map m ≫ ((Over.post (X := B.obj hS) B.inclusion).yonedaMapIso Y).hom
      = ((Over.post (X := B.obj hS) B.inclusion).yonedaMapIso X).hom ≫
        (Over.post (X := B.obj hS) B.inclusion).op.whiskerLeft
          (yoneda.map ((Over.post (X := B.obj hS) B.inclusion).map m)) := by
  ext A a
  exact (Over.post (X := B.obj hS) B.inclusion).map_comp a m

/-- The source and target of the pre-relation of a pair of morphisms of the site are the images of
the two morphisms. -/
private theorem relation_source_target (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {R U : BigFppfOver B S hS} (s t : R ⟶ U) :
    (relation B S hS s t).source = (Over.post (X := B.obj hS) B.inclusion).map s ∧
      (relation B S hS s t).target = (Over.post (X := B.obj hS) B.inclusion).map t :=
  ⟨prod.lift_snd _ _, prod.lift_fst _ _⟩

/-- The two legs of the pre-relation of a pair of morphisms of the site, read through the
comparison isomorphisms of `AlgebraicGeometry.Space.yonedaMapIso_naturality`. -/
private theorem sourceMap_targetMap_relation (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    {R U : BigFppfOver B S hS} (s t : R ⟶ U) :
    (yoneda.map s ≫ ((Over.post (X := B.obj hS) B.inclusion).yonedaMapIso U).hom
        = ((Over.post (X := B.obj hS) B.inclusion).yonedaMapIso R).hom ≫
          Stacks.Groupoids.sourceMap (Over.post B.inclusion) (relation B S hS s t)) ∧
      (yoneda.map t ≫ ((Over.post (X := B.obj hS) B.inclusion).yonedaMapIso U).hom
        = ((Over.post (X := B.obj hS) B.inclusion).yonedaMapIso R).hom ≫
          Stacks.Groupoids.targetMap (Over.post B.inclusion) (relation B S hS s t)) := by
  obtain ⟨hrs, hrt⟩ := relation_source_target B S hS s t
  refine ⟨?_, ?_⟩
  · rw [show Stacks.Groupoids.sourceMap (Over.post B.inclusion) (relation B S hS s t)
        = (Over.post (X := B.obj hS) B.inclusion).op.whiskerLeft
          (yoneda.map ((Over.post (X := B.obj hS) B.inclusion).map s)) by rw [← hrs]]
    exact yonedaMapIso_naturality B S hS s
  · rw [show Stacks.Groupoids.targetMap (Over.post B.inclusion) (relation B S hS s t)
        = (Over.post (X := B.obj hS) B.inclusion).op.whiskerLeft
          (yoneda.map ((Over.post (X := B.obj hS) B.inclusion).map t)) by rw [← hrt]]
    exact yonedaMapIso_naturality B S hS t

/-! ### Stacks 03BM for a relation on a one-point affine scheme -/

/-- **Stacks 03BM on a one-point affine scheme.** The fppf quotient sheaf of a finite locally
free equivalence relation on an affine scheme which is a single point and whose global
functions form a domain is represented by the spectrum of a subfield of those functions, in the
same big fppf site, compatibly with the canonical projection out of the objects.

The groupoid scheme and the `AlgebraicGeometry.ExtendsRelation` datum are inputs rather than
being built here, so that the two object equalities they carry can be substituted away; with
`AlgebraicGeometry.groupoidSchemeOfIsEquivalenceRelation` inlined they could not be, since the
groupoid would then depend on the objects being substituted. -/
@[sga "3 V 4.1" "special case"]
private theorem quotientRepresentation {S : Scheme.{u}} {R U : Over S} (j : PreRelation R U)
    (G : GroupoidScheme S) (hG : ExtendsRelation j G)
    (hequiv : IsEquivalenceRelation j.target j.source)
    (haU : IsAffine U.left) (haR : IsAffine R.left)
    (hsf : IsFiniteLocallyFree j.source.left) (htf : IsFiniteLocallyFree j.target.left)
    (hdom : IsDomain Γ(U.left, ⊤)) (hsub : Subsingleton ↥U.left)
    (B : BigFppfSite.{u}) (hS : B.Contains S) (hcU : B.Contains U.left)
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)] :
    ∃ (C : Subring Γ(U.left, ⊤)) (_ : IsField C)
      (hC : B.Contains (Spec (CommRingCat.of C))) (b' : Spec (CommRingCat.of C) ⟶ S)
      (hb' : (U.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom C.subtype)) ≫ b' = U.hom),
      ∃ hMs : Presheaf.IsSheaf (BigFppfOver.topology B S hS)
          (Stacks.Groupoids.points (Over.post (X := B.obj hS) B.inclusion)
            ((Over.post (X := B.obj hS) B.inclusion).obj
              (Over.mk (⟨b'⟩ : B.obj hC ⟶ B.obj hS)))),
        ∃ w : quotientSheaf (BigFppfOver.topology B S hS)
              (Over.post (X := B.obj hS) B.inclusion) j ⟶
            ⟨Stacks.Groupoids.points (Over.post (X := B.obj hS) B.inclusion)
              ((Over.post (X := B.obj hS) B.inclusion).obj
                (Over.mk (⟨b'⟩ : B.obj hC ⟶ B.obj hS))), hMs⟩,
          IsIso w ∧
            toQuotientSheaf (BigFppfOver.topology B S hS)
                (Over.post (X := B.obj hS) B.inclusion) j ≫ w.hom =
              (Over.post (X := B.obj hS) B.inclusion).op.whiskerLeft (yoneda.map
                (Over.homMk (U.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom C.subtype)) hb' :
                  U ⟶ (Over.post (X := B.obj hS) B.inclusion).obj
                    (Over.mk (⟨b'⟩ : B.obj hC ⟶ B.obj hS)))) := by
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
  have hcM : B.Contains (quotientOver G).left := contains_quotientOver G B hcU
  have hpb : IsPullback G.target G.source (quotientProjection G) (quotientProjection G) :=
    (affineFiniteFlatQuotient G).kernelPair
  have hrep := quotientSheaf_isRepresented_of_isPullback G (quotientProjection G)
    (affineFiniteFlatQuotient G).finiteLocallyFree (affineFiniteFlatQuotient G).surjective
    hpb B hS
  refine ⟨invariantRing G, isField_invariantRing G hdom hsub, hcM, (quotientBaseMap G).val,
    (quotientBaseMap G).property, ?_⟩
  rwa [← hj]

/-! ### Stacks 0262, part (3), as an isomorphism onto the quotient sheaf -/

/-- The descent datum of a morphism along its kernel pair: composed with the comparison of
`AlgebraicGeometry.Space.yonedaMapIso_naturality`, the morphism coequalizes the two legs of the
pre-relation. -/
private theorem sourceMap_comp_eq_targetMap_comp (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {R U : BigFppfOver B S hS} (f : yoneda.obj U ⟶ F)
    (s t : R ⟶ U) (hR : IsPullback (yoneda.map s) (yoneda.map t) f f) :
    Stacks.Groupoids.sourceMap (Over.post (X := B.obj hS) B.inclusion) (relation B S hS s t) ≫
        ((Over.post (X := B.obj hS) B.inclusion).yonedaMapIso U).inv ≫ f =
      Stacks.Groupoids.targetMap (Over.post (X := B.obj hS) B.inclusion) (relation B S hS s t) ≫
        ((Over.post (X := B.obj hS) B.inclusion).yonedaMapIso U).inv ≫ f := by
  obtain ⟨hs, ht⟩ := sourceMap_targetMap_relation B S hS s t
  have _ : (Over.post (X := B.obj hS) B.inclusion).Full := inferInstance
  have _ : (Over.post (X := B.obj hS) B.inclusion).Faithful := inferInstance
  set P : BigFppfOver B S hS ⥤ Over S := Over.post (X := B.obj hS) B.inclusion
  set j := relation B S hS s t
  set eU := P.yonedaMapIso U
  set eR := P.yonedaMapIso R
  set kk : Stacks.Groupoids.points P (P.obj U) ⟶ F := eU.inv ≫ f with hkk
  rw [← cancel_epi eR.hom]
  calc eR.hom ≫ Stacks.Groupoids.sourceMap P j ≫ kk
      = (eR.hom ≫ Stacks.Groupoids.sourceMap P j) ≫ kk := (Category.assoc _ _ _).symm
    _ = (yoneda.map s ≫ eU.hom) ≫ kk := by rw [← hs]
    _ = yoneda.map s ≫ f := by rw [hkk, Category.assoc, Iso.hom_inv_id_assoc]
    _ = yoneda.map t ≫ f := hR.w
    _ = (yoneda.map t ≫ eU.hom) ≫ kk := by
          rw [hkk, Category.assoc, Iso.hom_inv_id_assoc]
    _ = (eR.hom ≫ Stacks.Groupoids.targetMap P j) ≫ kk := by rw [← ht]
    _ = eR.hom ≫ Stacks.Groupoids.targetMap P j ≫ kk := Category.assoc _ _ _

/-- The two legs of the kernel pair, followed by the comparison of
`AlgebraicGeometry.Space.yonedaMapIso_naturality` and the projection to the quotient sheaf of the
pre-relation, agree. -/
private theorem yoneda_map_comp_toQuotientSheaf (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    {R U : BigFppfOver B S hS} (s t : R ⟶ U) :
    yoneda.map s ≫ ((Over.post (X := B.obj hS) B.inclusion).yonedaMapIso U).hom ≫
        toQuotientSheaf (BigFppfOver.topology B S hS) (Over.post (X := B.obj hS) B.inclusion)
          (relation B S hS s t) =
      yoneda.map t ≫ ((Over.post (X := B.obj hS) B.inclusion).yonedaMapIso U).hom ≫
        toQuotientSheaf (BigFppfOver.topology B S hS) (Over.post (X := B.obj hS) B.inclusion)
          (relation B S hS s t) := by
  obtain ⟨hs, ht⟩ := sourceMap_targetMap_relation B S hS s t
  set J := BigFppfOver.topology B S hS
  have _ : (Over.post (X := B.obj hS) B.inclusion).Full := inferInstance
  have _ : (Over.post (X := B.obj hS) B.inclusion).Faithful := inferInstance
  set P : BigFppfOver B S hS ⥤ Over S := Over.post (X := B.obj hS) B.inclusion
  set j := relation B S hS s t
  set eU := P.yonedaMapIso U
  set eR := P.yonedaMapIso R
  calc yoneda.map s ≫ eU.hom ≫ toQuotientSheaf J P j
      = (yoneda.map s ≫ eU.hom) ≫ toQuotientSheaf J P j := (Category.assoc _ _ _).symm
    _ = (eR.hom ≫ Stacks.Groupoids.sourceMap P j) ≫ toQuotientSheaf J P j := by rw [← hs]
    _ = eR.hom ≫ Stacks.Groupoids.sourceMap P j ≫ toQuotientSheaf J P j :=
          Category.assoc _ _ _
    _ = eR.hom ≫ Stacks.Groupoids.targetMap P j ≫ toQuotientSheaf J P j := by
          rw [sourceMap_toQuotientSheaf]
    _ = (eR.hom ≫ Stacks.Groupoids.targetMap P j) ≫ toQuotientSheaf J P j :=
          (Category.assoc _ _ _).symm
    _ = (yoneda.map t ≫ eU.hom) ≫ toQuotientSheaf J P j := by rw [← ht]
    _ = yoneda.map t ≫ eU.hom ≫ toQuotientSheaf J P j := Category.assoc _ _ _

/-- **An algebraic space is the quotient sheaf of the kernel pair of a surjective étale
atlas.** The descent of the atlas to the quotient sheaf of its kernel pair is an isomorphism.

The inverse comes from the coequalizer property of the atlas, Stacks 0262 part (3); that the
two composites are identities is then the uniqueness halves of the two universal properties,
`Stacks.Groupoids.quotientSheafDesc_unique` for one and
`CategoryTheory.Limits.Cofork.IsColimit.hom_ext` for the other. -/
private theorem isIso_quotientSheafDesc (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    {R U : BigFppfOver B S hS} (f : yoneda.obj U ⟶ F) (s t : R ⟶ U)
    (hR : IsPullback (yoneda.map s) (yoneda.map t) f f)
    (hsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f)
    (hetale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f) :
    ∃ d : quotientSheaf (BigFppfOver.topology B S hS) (Over.post (X := B.obj hS) B.inclusion)
        (relation B S hS s t) ⟶
        (⟨F, hF.isSheaf⟩ : Sheaf (BigFppfOver.topology B S hS) (Type u)),
      IsIso d ∧
      toQuotientSheaf (BigFppfOver.topology B S hS)
          (Over.post (X := B.obj hS) B.inclusion) (relation B S hS s t) ≫ d.hom =
        ((Over.post (X := B.obj hS) B.inclusion).yonedaMapIso U).inv ≫ f := by
  set J := BigFppfOver.topology B S hS
  have _ : (Over.post (X := B.obj hS) B.inclusion).Full := inferInstance
  have _ : (Over.post (X := B.obj hS) B.inclusion).Faithful := inferInstance
  set P : BigFppfOver B S hS ⥤ Over S := Over.post (X := B.obj hS) B.inclusion
  set j := relation B S hS s t
  set eU := P.yonedaMapIso U
  set kk : Stacks.Groupoids.points P (P.obj U) ⟶ F := eU.inv ≫ f with hkk
  have hcond : Stacks.Groupoids.sourceMap P j ≫ kk = Stacks.Groupoids.targetMap P j ≫ kk :=
    sourceMap_comp_eq_targetMap_comp B S hS f s t hR
  set d := quotientSheafDesc J P j ⟨F, hF.isSheaf⟩ kk hcond
  have hdfac : toQuotientSheaf J P j ≫ d.hom = kk :=
    toQuotientSheaf_quotientSheafDesc J P j ⟨F, hF.isSheaf⟩ kk hcond
  obtain ⟨hRsh, hUsh, hcolim⟩ :=
    isCoequalizer_of_surjectiveEtale B S hS f s t hR hF hsurj hetale
  obtain ⟨hco⟩ := hcolim
  refine ⟨d, ?_, hdfac⟩
  set qp : (⟨yoneda.obj U, hUsh⟩ : Sheaf J (Type u)) ⟶ quotientSheaf J P j :=
    ⟨eU.hom ≫ toQuotientSheaf J P j⟩
  have hqpc : (⟨yoneda.map s⟩ : (⟨yoneda.obj R, hRsh⟩ : Sheaf J (Type u)) ⟶ ⟨yoneda.obj U, hUsh⟩)
      ≫ qp = (⟨yoneda.map t⟩ :
        (⟨yoneda.obj R, hRsh⟩ : Sheaf J (Type u)) ⟶ ⟨yoneda.obj U, hUsh⟩) ≫ qp := by
    apply Sheaf.hom_ext
    change yoneda.map s ≫ eU.hom ≫ toQuotientSheaf J P j
      = yoneda.map t ≫ eU.hom ≫ toQuotientSheaf J P j
    exact yoneda_map_comp_toQuotientSheaf B S hS s t
  set e' := Cofork.IsColimit.desc hco qp hqpc
  have hfe' : (⟨f⟩ : (⟨yoneda.obj U, hUsh⟩ : Sheaf J (Type u)) ⟶ ⟨F, hF.isSheaf⟩) ≫ e' = qp :=
    Cofork.IsColimit.π_desc' hco qp hqpc
  have hfe'' : f ≫ e'.hom = eU.hom ≫ toQuotientSheaf J P j := Sheaf.hom_ext_iff.mp hfe'
  refine ⟨e', ?_, ?_⟩
  · have h1 : toQuotientSheaf J P j ≫ (d ≫ e').hom = toQuotientSheaf J P j := by
      change toQuotientSheaf J P j ≫ d.hom ≫ e'.hom = toQuotientSheaf J P j
      rw [← Category.assoc, hdfac, hkk, Category.assoc, hfe'', Iso.inv_hom_id_assoc]
    rw [quotientSheafDesc_unique J P j _ (toQuotientSheaf J P j)
        (sourceMap_toQuotientSheaf J P j) (d ≫ e') h1,
      quotientSheafDesc_unique J P j _ (toQuotientSheaf J P j)
        (sourceMap_toQuotientSheaf J P j) (𝟙 _) (by simp)]
  · refine Cofork.IsColimit.hom_ext hco ?_
    rw [Cofork.π_ofπ, ← Category.assoc, hfe']
    apply Sheaf.hom_ext
    change (eU.hom ≫ toQuotientSheaf J P j) ≫ d.hom = f ≫ 𝟙 F
    rw [Category.assoc, hdfac, hkk, Iso.hom_inv_id_assoc, Category.comp_id]

/-! ### The core statement, for an atlas with one point -/

/-- Over an algebraic space quasi-separated over `S`, both legs of the kernel pair of a morphism
out of an object of the site whose underlying scheme is a single point are quasi-compact. -/
private theorem quasiCompact_legs_of_isPullback (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hqs : IsQuasiSeparatedOver B S hS F) {R U : BigFppfOver B S hS}
    (hsubU : Subsingleton ↥((Over.post (X := B.obj hS) B.inclusion).obj U).left)
    (f : yoneda.obj U ⟶ F) (s t : R ⟶ U) (hR : IsPullback (yoneda.map s) (yoneda.map t) f f) :
    QuasiCompact ((BigFppfOver.toScheme B S hS).map s) ∧
      QuasiCompact ((BigFppfOver.toScheme B S hS).map t) := by
  have _ : HasBinaryProducts (BigFppfOver B S hS) :=
    CategoryTheory.Over.ConstructProducts.over_binaryProduct_of_pullback
  have hlift : yoneda.map (prod.lift s t) ≫
      prodComparison (yoneda : BigFppfOver B S hS ⥤ _) U U
      = prod.lift (yoneda.map s) (yoneda.map t) := by
    refine prod.hom_ext ?_ ?_
    · rw [Category.assoc, prodComparison_fst, ← yoneda.map_comp, prod.lift_fst, prod.lift_fst]
    · rw [Category.assoc, prodComparison_snd, ← yoneda.map_comp, prod.lift_snd, prod.lift_snd]
  have hQCrel : QuasiCompact ((BigFppfOver.toScheme B S hS).map
      (prod.lift s t : R ⟶ U ⨯ U)) := by
    have hsq : IsPullback (yoneda.map s ≫ f) (yoneda.map (prod.lift s t)) (diag F)
        (prodComparison (yoneda : BigFppfOver B S hS ⥤ _) U U ≫ prod.map f f) := by
      refine isPullback_of_iso_right ?_
      rw [hlift]
      exact isPullback_diag f hR
    exact hqs.property _ (yoneda.map s ≫ f) (prod.lift s t) hsq
  have hQCb : QuasiCompact (B.inclusion.map U.hom) := by
    constructor
    intro V _ _
    have hsub : ((B.inclusion.map U.hom).base ⁻¹' V).Subsingleton :=
      fun a _ c _ ↦ hsubU.allEq a c
    exact hsub.finite.isCompact
  have hpbUU : IsPullback ((prod.fst : U ⨯ U ⟶ U)).left ((prod.snd : U ⨯ U ⟶ U)).left
      U.hom U.hom :=
    CategoryTheory.Over.isPullback_of_binaryFan_isLimit (BinaryFan.mk prod.fst prod.snd)
      (prodIsProd U U)
  refine ⟨?_, ?_⟩
  · rw [show s = (prod.lift s t : R ⟶ U ⨯ U) ≫ prod.fst from (prod.lift_fst _ _).symm,
      (BigFppfOver.toScheme B S hS).map_comp]
    have _ : QuasiCompact ((BigFppfOver.toScheme B S hS).map (prod.fst : U ⨯ U ⟶ U)) :=
      MorphismProperty.of_isPullback (hpbUU.map B.inclusion).flip hQCb
    infer_instance
  · rw [show t = (prod.lift s t : R ⟶ U ⨯ U) ≫ prod.snd from (prod.lift_snd _ _).symm,
      (BigFppfOver.toScheme B S hS).map_comp]
    have _ : QuasiCompact ((BigFppfOver.toScheme B S hS).map (prod.snd : U ⨯ U ⟶ U)) :=
      MorphismProperty.of_isPullback (hpbUU.map B.inclusion) hQCb
    infer_instance

/-- Two isomorphisms out of the quotient sheaf of a relation, one onto a sheaf `F` and one onto a
representable sheaf, compatible with the canonical projections, assemble into an isomorphism of
`F` with the representable sheaf carrying a given morphism to the given representable one. -/
private theorem exists_iso_of_quotientSheaf (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    {R U V : BigFppfOver B S hS} (f : yoneda.obj U ⟶ F) (s t : R ⟶ U) (m : U ⟶ V)
    (hV : Presheaf.IsSheaf (BigFppfOver.topology B S hS)
      (Stacks.Groupoids.points (Over.post (X := B.obj hS) B.inclusion)
        ((Over.post (X := B.obj hS) B.inclusion).obj V)))
    (d : quotientSheaf (BigFppfOver.topology B S hS) (Over.post (X := B.obj hS) B.inclusion)
        (relation B S hS s t) ⟶ (⟨F, hF⟩ : Sheaf (BigFppfOver.topology B S hS) (Type u)))
    (hd : IsIso d)
    (hdfac : toQuotientSheaf (BigFppfOver.topology B S hS)
        (Over.post (X := B.obj hS) B.inclusion) (relation B S hS s t) ≫ d.hom =
      ((Over.post (X := B.obj hS) B.inclusion).yonedaMapIso U).inv ≫ f)
    (w : quotientSheaf (BigFppfOver.topology B S hS) (Over.post (X := B.obj hS) B.inclusion)
        (relation B S hS s t) ⟶
      ⟨Stacks.Groupoids.points (Over.post (X := B.obj hS) B.inclusion)
        ((Over.post (X := B.obj hS) B.inclusion).obj V), hV⟩)
    (hw : IsIso w)
    (hwfac : toQuotientSheaf (BigFppfOver.topology B S hS)
        (Over.post (X := B.obj hS) B.inclusion) (relation B S hS s t) ≫ w.hom =
      (Over.post (X := B.obj hS) B.inclusion).op.whiskerLeft
        (yoneda.map ((Over.post (X := B.obj hS) B.inclusion).map m))) :
    ∃ e : F ≅ yoneda.obj V, f ≫ e.hom = yoneda.map m := by
  have hdhi : d.hom ≫ (inv d).hom = 𝟙 _ := Sheaf.hom_ext_iff.mp (IsIso.hom_inv_id d)
  have hdih : (inv d).hom ≫ d.hom = 𝟙 _ := Sheaf.hom_ext_iff.mp (IsIso.inv_hom_id d)
  have hwhi : w.hom ≫ (inv w).hom = 𝟙 _ := Sheaf.hom_ext_iff.mp (IsIso.hom_inv_id w)
  have hwih : (inv w).hom ≫ w.hom = 𝟙 _ := Sheaf.hom_ext_iff.mp (IsIso.inv_hom_id w)
  have _ : IsIso (inv d).hom := ⟨d.hom, hdih, hdhi⟩
  have _ : IsIso w.hom := ⟨(inv w).hom, hwhi, hwih⟩
  have hfd : f ≫ (inv d).hom
      = ((Over.post (X := B.obj hS) B.inclusion).yonedaMapIso U).hom ≫
        toQuotientSheaf (BigFppfOver.topology B S hS)
          (Over.post (X := B.obj hS) B.inclusion) (relation B S hS s t) := by
    rw [show f = ((Over.post (X := B.obj hS) B.inclusion).yonedaMapIso U).hom ≫
        toQuotientSheaf (BigFppfOver.topology B S hS)
          (Over.post (X := B.obj hS) B.inclusion) (relation B S hS s t) ≫ d.hom by
      rw [hdfac, Iso.hom_inv_id_assoc]]
    simp only [Category.assoc, hdhi, Category.comp_id]
  refine ⟨asIso ((inv d).hom ≫ w.hom ≫
    ((Over.post (X := B.obj hS) B.inclusion).yonedaMapIso V).inv), ?_⟩
  have key : (f ≫ (inv d).hom) ≫ w.hom
      = ((Over.post (X := B.obj hS) B.inclusion).yonedaMapIso U).hom ≫
        (Over.post (X := B.obj hS) B.inclusion).op.whiskerLeft
          (yoneda.map ((Over.post (X := B.obj hS) B.inclusion).map m)) := by
    rw [hfd, Category.assoc, hwfac]
  simp only [asIso_hom, ← Category.assoc]
  rw [key]
  exact (Iso.comp_inv_eq _).mpr (yonedaMapIso_naturality B S hS m).symm

/-- **Stacks 03DZ, for an atlas which is affine, locally Artinian, a single point, and has a
domain of functions.** An algebraic space over `S` which is quasi-separated over `S` and
admits a surjective étale morphism from such an object of the site is represented by the
spectrum of the field of invariant functions on the atlas, with the representing isomorphism
carrying the atlas to the canonical morphism out of it. -/
private theorem pointLikeCore (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hqs : IsQuasiSeparatedOver B S hS F)
    (U : BigFppfOver B S hS)
    (haU : IsAffine ((Over.post (X := B.obj hS) B.inclusion).obj U).left)
    (hartU : IsLocallyArtinian ((Over.post (X := B.obj hS) B.inclusion).obj U).left)
    (hsubU : Subsingleton ↥((Over.post (X := B.obj hS) B.inclusion).obj U).left)
    (hdomU : IsDomain Γ(((Over.post (X := B.obj hS) B.inclusion).obj U).left, ⊤))
    (f : yoneda.obj U ⟶ F)
    (hsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f)
    (hetale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f) :
    ∃ (k' : Type u) (_ : Field k') (hC : B.Contains (Spec (CommRingCat.of k')))
      (b' : Spec (CommRingCat.of k') ⟶ S)
      (g : ((Over.post (X := B.obj hS) B.inclusion).obj U).left ⟶ Spec (CommRingCat.of k'))
      (hb' : g ≫ b' = ((Over.post (X := B.obj hS) B.inclusion).obj U).hom)
      (e : F ≅ yoneda.obj (Over.mk (⟨b'⟩ : B.obj hC ⟶ B.obj hS))),
      f ≫ e.hom = yoneda.map (Over.homMk
        (ObjectProperty.homMk g : U.left ⟶ B.obj hC) (by
          apply ObjectProperty.hom_ext
          exact hb')) := by
  classical
  have _ : HasSheafify (BigFppfOver.topology B S hS) (Type u) :=
    BigFppfOver.hasSheafify_type B S hS
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := haU
  have _ : IsLocallyArtinian ((BigFppfOver.toScheme B S hS).obj U) := hartU
  obtain ⟨R, s, t, hR⟩ : ∃ (R : BigFppfOver B S hS) (s t : R ⟶ U),
      IsPullback (yoneda.map s) (yoneda.map t) f f := by
    have hq := hF.diagonal_representable.of_diag f
    exact ⟨hq.pullback f, yoneda.preimage (hq.fst f), hq.snd f, by
      simpa using hq.isPullback f⟩
  have hEs : Etale ((BigFppfOver.toScheme B S hS).map s) :=
    hetale.property f (yoneda.map t) s hR.flip
  have hEt : Etale ((BigFppfOver.toScheme B S hS).map t) :=
    hetale.property f (yoneda.map s) t hR
  obtain ⟨hQCs, hQCt⟩ := quasiCompact_legs_of_isPullback B S hS hqs hsubU f s t hR
  obtain ⟨hflfs, haffR⟩ :=
    isFiniteLocallyFree_of_etale_quasiCompact ((BigFppfOver.toScheme B S hS).map s)
  obtain ⟨hflft, -⟩ :=
    isFiniteLocallyFree_of_etale_quasiCompact ((BigFppfOver.toScheme B S hS).map t)
  obtain ⟨hrs, hrt⟩ := relation_source_target B S hS s t
  have hequiv : IsEquivalenceRelation (relation B S hS s t).target
      (relation B S hS s t).source := by
    rw [hrt, hrs]
    exact isEquivalenceRelation_of_isPullback B S hS f t s hR.flip
  -- Stacks 03BM: the quotient sheaf is the spectrum of the field of invariant functions
  obtain ⟨C, hCfield, hC, b', hb', hMs, w, hwiso, hwfac⟩ :=
    quotientRepresentation (S := S) (relation B S hS s t)
      (groupoidSchemeOfIsEquivalenceRelation (relation B S hS s t))
      (groupoidSchemeOfIsEquivalenceRelation_extendsRelation _)
      hequiv haU haffR (by rwa [hrs]) (by rwa [hrt]) hdomU hsubU B hS U.left.property
  -- Stacks 0262 part (3): the algebraic space itself is that quotient sheaf
  obtain ⟨d, hdiso, hdfac⟩ := isIso_quotientSheafDesc B S hS hF f s t hR hsurj hetale
  obtain ⟨e, he⟩ := exists_iso_of_quotientSheaf B S hS hF.isSheaf f s t
    (Over.homMk (ObjectProperty.homMk
      (((Over.post (X := B.obj hS) B.inclusion).obj U).left.toSpecΓ ≫
        Spec.map (CommRingCat.ofHom C.subtype)) : U.left ⟶ B.obj hC) (by
          apply ObjectProperty.hom_ext
          exact hb') : U ⟶ Over.mk (⟨b'⟩ : B.obj hC ⟶ B.obj hS))
    hMs d hdiso hdfac w hwiso hwfac
  exact ⟨C, hCfield.toField, hC, b', _, hb', e, he⟩

/-- **A field extension whose induced morphism of spectra is étale is finite separable.**
Over a field, an étale ring map is formally étale and of finite presentation, hence formally
unramified and essentially of finite type, so the extension is finite; and formal étaleness of
an essentially-of-finite-type field extension is separability. -/
@[ega "0 19.10.3" "(iii), special case", ega "0 21.7.4" "c ⇒ a", sga "3 VIIB 1.6" "(i)⇒(iv)"]
private theorem finite_separable_of_etale_algebraMap (k' k : Type u) [Field k'] [Field k]
    [Algebra k' k] (h : Etale (Spec.map (CommRingCat.ofHom (algebraMap k' k)))) :
    Module.Finite k' k ∧ Algebra.IsSeparable k' k := by
  have hEt : (CommRingCat.ofHom (algebraMap k' k)).hom.Etale :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mp h
  change (algebraMap k' k).Etale at hEt
  rw [RingHom.etale_algebraMap] at hEt
  obtain ⟨hfe, hfp⟩ := hEt
  exact ⟨Algebra.FormallyUnramified.finite_of_free k' k,
    (Algebra.FormallyEtale.iff_isSeparable k' k).mp inferInstance⟩

/-! ### Stacks 03DZ -/

/-- **Stacks 03DZ.** Let `S` be a scheme, `k` a field and `X` an algebraic space over `S`
admitting a surjective étale morphism `Spec(k) ⟶ X`. If `X` is quasi-separated over `S`, then
`X` is isomorphic to `Spec(k')` for a field `k'` with `k/k'` finite separable, the isomorphism
carrying the given atlas to the morphism induced by the field extension.

The hypothesis is quasi-separatedness over `S` — Stacks 02X5, that the diagonal
`X ⟶ X ×_S X` is quasi-compact after every representable base change — which is what the
source's proof consumes, and is weaker than quasi-separatedness over `Spec(ℤ)`, Stacks 03BS
part (3); see the implementation notes of this file. -/
theorem exists_field_spectrum_of_surjective_etale_of_isQuasiSeparatedOver
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hqs : IsQuasiSeparatedOver B S hS F)
    (k : Type u) [Field k] (hk : B.Contains (Spec (CommRingCat.of k)))
    (b : Spec (CommRingCat.of k) ⟶ S)
    (f : yoneda.obj (Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS)) ⟶ F)
    (hsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f)
    (hetale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f) :
    ∃ (k' : Type u) (_ : Field k') (_ : Algebra k' k)
      (_ : Module.Finite k' k) (_ : Algebra.IsSeparable k' k)
      (hk' : B.Contains (Spec (CommRingCat.of k')))
      (b' : Spec (CommRingCat.of k') ⟶ S),
      ∃ (hbase : Spec.map (CommRingCat.ofHom (algebraMap k' k)) ≫ b' = b)
        (e : F ≅ yoneda.obj (Over.mk (⟨b'⟩ : B.obj hk' ⟶ B.obj hS))),
        f ≫ e.hom = yoneda.map (Over.homMk
          (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap k' k))) :
            B.obj hk ⟶ B.obj hk') (by
              apply ObjectProperty.hom_ext
              exact hbase)) := by
  classical
  obtain ⟨k', hk'field, hC, b', g, hb', e, hcompat⟩ :=
    pointLikeCore B S hS hF hqs (Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS))
      (inferInstance : IsAffine (Spec (CommRingCat.of k)))
      (inferInstance : IsLocallyArtinian (Spec (CommRingCat.of k)))
      (inferInstance : Subsingleton ↥(Spec (CommRingCat.of k)))
      (((Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv).toMulEquiv.isDomain k)
      f hsurj hetale
  obtain ⟨ψ, rfl⟩ :=
    Spec.map_surjective (R := CommRingCat.of k') (S := CommRingCat.of k) g
  have _ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have _ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).RespectsIso :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hEm : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (f ≫ e.hom) :=
    MorphismProperty.RespectsIso.postcomp _ e.hom f hetale
  rw [hcompat] at hEm
  have hEtm0 := MorphismProperty.of_relative_map hEm
  have hEtm : Etale (Spec.map ψ) := hEtm0
  have hfs := @finite_separable_of_etale_algebraMap k' k hk'field _ ψ.hom.toAlgebra hEtm
  exact ⟨k', hk'field, ψ.hom.toAlgebra, hfs.1, hfs.2, hC, b', hb', e, hcompat⟩

/-- **Stacks 03DZ.** Let `S` be a scheme, `k` a field and `X` an algebraic space over `S`
admitting a surjective étale morphism `Spec(k) ⟶ X`. If `X` is quasi-separated — Stacks 03BS
part (3), that is, quasi-separated over `Spec(ℤ)` — then `X` is isomorphic to `Spec(k')` for a
field `k'` with `k/k'` finite separable, the isomorphism carrying the given atlas to the
morphism induced by the field extension.

This is
`AlgebraicGeometry.Space.exists_field_spectrum_of_surjective_etale_of_isQuasiSeparatedOver`,
which asks only for quasi-separatedness over `S` and is therefore stronger, together with
`AlgebraicGeometry.Space.isQuasiSeparatedOver_of_isAbsolutelyQuasiSeparated`.
Surjectivity is taken in the sense of Stacks 03ME, that the induced map on points is
surjective, which is the source's reading; the engine asks instead that every represented base
change be a surjective morphism of schemes, and the two agree for a morphism into an algebraic
space by `AlgebraicGeometry.Space.presheafSurjective_of_isSurjective`, whose representability
hypothesis is supplied by the representable diagonal of `X`. -/
@[stacks 03DZ]
theorem exists_field_spectrum_of_surjective_etale
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ F)
    (k : Type u) [Field k] (hk : B.Contains (Spec (CommRingCat.of k)))
    (b : Spec (CommRingCat.of k) ⟶ S)
    (f : yoneda.obj (Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS)) ⟶ F)
    (hsurj : IsSurjective B S hS f)
    (hetale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f) :
    ∃ (k' : Type u) (_ : Field k') (_ : Algebra k' k)
      (_ : Module.Finite k' k) (_ : Algebra.IsSeparable k' k)
      (hk' : B.Contains (Spec (CommRingCat.of k')))
      (b' : Spec (CommRingCat.of k') ⟶ S),
      ∃ (hbase : Spec.map (CommRingCat.ofHom (algebraMap k' k)) ≫ b' = b)
        (e : F ≅ yoneda.obj (Over.mk (⟨b'⟩ : B.obj hk' ⟶ B.obj hS))),
        f ≫ e.hom = yoneda.map (Over.homMk
          (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap k' k))) :
            B.obj hk ⟶ B.obj hk') (by
              apply ObjectProperty.hom_ext
              exact hbase)) :=
  exists_field_spectrum_of_surjective_etale_of_isQuasiSeparatedOver B S hS hF
    (isQuasiSeparatedOver_of_isAbsolutelyQuasiSeparated B S hS hZ hF hqs) k hk b f
    (presheafSurjective_of_isSurjective B S hS f (hF.diagonal_representable.of_diag f) hsurj)
    hetale

end AlgebraicGeometry.Space

end
