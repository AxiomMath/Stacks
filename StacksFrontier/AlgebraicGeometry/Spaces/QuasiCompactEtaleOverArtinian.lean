module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleQuasiFinite
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleFieldAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.AffineArtinian
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Quasi-compact quasi-separated algebraic spaces étale over an Artinian scheme

Let `V` be an object of the big fppf site over `S` whose underlying scheme is affine and locally
Artinian, that is the spectrum of an Artinian ring.  An algebraic space `W` over `S` which is
quasi-compact, quasi-separated and étale over `V` is represented by an object of the site whose
underlying scheme is affine.

This is the case of Stacks 06LZ, part (3), that the proof of Stacks 09TL, part (1) uses: there
`W = Z ×_X U` is the base change of the spectrum `Z` of an Artinian ring along a quasi-compact
and quasi-separated étale `U ⟶ X`, and the source asserts that it is affine.

## Main results

* `AlgebraicGeometry.Space.exists_iso_yoneda_isAffine_of_etale_over_isLocallyArtinian`: a
  quasi-compact and quasi-separated algebraic space étale over an affine locally Artinian object
  of the site is represented by an object whose scheme is affine.

## Implementation notes

The proof is the one of Stacks 06LZ, part (3).  A quasi-compact algebraic space has a surjective
étale atlas `a : h_A ⟶ W` with `A` quasi-compact.  The composite `A ⟶ V` is étale, hence locally
quasi-finite, and quasi-compact, so it is finite over the locally Artinian `V`
(`AlgebraicGeometry.IsFinite.of_locallyQuasiFinite`); in particular `A` is affine and locally
Artinian.  Quasi-separatedness of `W` makes the kernel pair `R = A ×_W A` quasi-compact, and the
same argument applied to its two étale projections to the locally Artinian `A` shows that they
are finite, hence finite locally free, with affine source.  The relation is an equivalence
relation, so Stacks 03BM
(`AlgebraicGeometry.Space.exists_quotient_of_isFiniteLocallyFree_relation`) produces an affine
quotient with the same kernel pair, and the atlas exhibits `W` as that quotient
(`AlgebraicGeometry.Space.exists_iso_yoneda_of_isPullback`).

## References

* [Stacks Project, Tag 06LZ](https://stacks.math.columbia.edu/tag/06LZ)
* [Stacks Project, Tag 03BM](https://stacks.math.columbia.edu/tag/03BM)
* [Stacks Project, Tag 09TL](https://stacks.math.columbia.edu/tag/09TL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A quasi-compact étale morphism of schemes into a locally Artinian scheme is finite, and its
source is locally Artinian: étale morphisms are locally quasi-finite, so this is
`AlgebraicGeometry.IsFinite.of_locallyQuasiFinite`, with local quasi-finiteness supplied by
`AlgebraicGeometry.locallyQuasiFinite_of_etale`. -/
@[sga "3 VIB 1.4.1" "(i) ⇒ (v), special case"]
theorem isFinite_isLocallyArtinian_of_etale_of_quasiCompact {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Etale f] [QuasiCompact f] [IsLocallyArtinian Y] :
    _root_.AlgebraicGeometry.IsFinite f ∧ IsLocallyArtinian X :=
  have := (_root_.AlgebraicGeometry.locallyQuasiFinite_of_etale f).2
  ⟨.of_locallyQuasiFinite f, .of_locallyQuasiFinite f⟩

/-- An étale morphism from a quasi-compact scheme to an affine locally Artinian scheme is finite
locally free, and its source is affine and locally Artinian. -/
theorem isFiniteLocallyFree_isAffine_of_etale_of_compactSpace {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Etale f] [IsAffine Y] [IsLocallyArtinian Y] (hX : CompactSpace X) :
    Stacks.Morphisms.IsFiniteLocallyFree f ∧ IsAffine X ∧ IsLocallyArtinian X := by
  have : QuasiCompact f := quasiCompact_of_compactSpace_of_isAffine f inferInstance hX
  obtain ⟨hfin, hart⟩ := isFinite_isLocallyArtinian_of_etale_of_quasiCompact f
  refine ⟨?_, isAffine_of_isAffineHom f, hart⟩
  rw [Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation]
  exact ⟨hfin, inferInstance, inferInstance⟩

/-- **A quasi-compact and quasi-separated algebraic space étale over the spectrum of an Artinian
ring is affine.**

Let `V` be an object of the big fppf site over `S` whose underlying scheme is affine and locally
Artinian, and let `p : W ⟶ h_V` be an étale morphism from a quasi-compact and quasi-separated
algebraic space.  Then `W` is represented by an object of the site whose underlying scheme is
affine.  This is the case of Stacks 06LZ, part (3), used in the proof of Stacks 09TL. -/
theorem exists_iso_yoneda_isAffine_of_etale_over_isLocallyArtinian
    (hZ : B.Contains (⊤_ Scheme.{u}))
    {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hW : IsAlgebraicSpace B S hS W)
    {V : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [IsLocallyArtinian ((BigFppfOver.toScheme B S hS).obj V)]
    (p : W ⟶ yoneda.obj V) (hp : IsEtale B S hS p)
    (hqc : IsQuasiCompactSpace B S hS W) (hqs : IsAbsolutelyQuasiSeparated B S hS hZ W) :
    ∃ (U : BigFppfOver B S hS) (_ : W ≅ yoneda.obj U),
      IsAffine ((BigFppfOver.toScheme B S hS).obj U) := by
  classical
  have _ : MorphismProperty.RespectsIso
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  obtain ⟨A, a, hAcpt, hasurj, haet⟩ := hqc
  have haet' := presheaf_etale_of_isEtale B S hS haet
  obtain ⟨m, hm⟩ : ∃ m : A ⟶ V, yoneda.map m = a ≫ p :=
    ⟨yoneda.preimage (a ≫ p), yoneda.map_preimage _⟩
  have hmEt : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map m) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ m).1
      (by rw [hm]; exact hp A a haet')
  obtain ⟨-, hAaff, hAart⟩ := isFiniteLocallyFree_isAffine_of_etale_of_compactSpace
    ((BigFppfOver.toScheme B S hS).map m) hAcpt
  have hrep : yoneda.relativelyRepresentable a := hasurj.rep
  set R : BigFppfOver B S hS := hrep.pullback a
  set t : R ⟶ A := hrep.fst' a
  set s : R ⟶ A := hrep.snd a
  have hR : IsPullback (yoneda.map t) (yoneda.map s) a a := hrep.isPullback' a
  have hRcpt : CompactSpace ((BigFppfOver.toScheme B S hS).obj R) :=
    compactSpace_of_isAbsolutelyQuasiSeparated B S hS hZ hqs hR hAcpt hAcpt
  have hfl : ∀ x y : R ⟶ A, IsPullback (yoneda.map x) (yoneda.map y) a a →
      Stacks.Morphisms.IsFiniteLocallyFree ((Over.post B.inclusion).map y).left ∧
        IsAffine ((Over.post B.inclusion).obj R).left := fun x y h =>
    have : Etale _ := haet'.property a (yoneda.map x) y h
    (isFiniteLocallyFree_isAffine_of_etale_of_compactSpace
      ((BigFppfOver.toScheme B S hS).map y) hRcpt).imp_right And.left
  have _ : IsAffine ((Over.post B.inclusion).obj A).left := hAaff
  have _ := (hfl t s hR).2
  have _ := (hfl t s hR).1
  have _ := (hfl s t hR.flip).1
  have _ : IsEquivalenceRelation ((Over.post B.inclusion).map t)
      ((Over.post B.inclusion).map s) :=
    isEquivalenceRelation_of_isPullback B S hS a t s hR
  obtain ⟨A₀, _, g, π, hsize, hflfπ, hsurjπ, hpb⟩ :=
    exists_quotient_of_isFiniteLocallyFree_relation S
      ((Over.post B.inclusion).map t) ((Over.post B.inclusion).map s)
  have hA₀ : B.Contains (Spec (CommRingCat.of A₀)) := lt_of_le_of_lt hsize A.left.2
  have _ := hflfπ
  obtain ⟨-, e, -, -⟩ :=
    exists_iso_yoneda_of_isPullback B S hS hW a t s hR hasurj haet'
      (U' := (Over.mk (⟨g⟩ : B.obj hA₀ ⟶ B.obj hS) : BigFppfOver B S hS)) π
      (Stacks.Morphisms.IsFiniteLocallyFree.flat π.left)
      (Stacks.Morphisms.IsFiniteLocallyFree.locallyOfFinitePresentation π.left) hsurjπ hpb
  exact ⟨_, e, inferInstanceAs (IsAffine (Spec (CommRingCat.of A₀)))⟩

/-- The local criterion behind `AlgebraicGeometry.Space.isAffineHom_of_isLocallyArtinian`: the
base change of a morphism from an affine locally Artinian object to a quasi-separated algebraic
space along an étale morphism from an affine object is represented by an affine object. -/
theorem exists_isPullback_affine_of_isLocallyArtinian (hZ : B.Contains (⊤_ Scheme.{u}))
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ F) (U : BigFppfOver B S hS)
    [hUaff : IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    [IsLocallyArtinian ((BigFppfOver.toScheme B S hS).obj U)]
    (f : yoneda.obj U ⟶ F) (V : AlgebraicGeometry.BigAffineFppf B S hS)
    (g : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj V) ⟶ F)
    (hg : AlgebraicGeometry.Space.IsEtale B S hS g) :
    ∃ (W : AlgebraicGeometry.BigAffineFppf B S hS)
      (p' : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj W) ⟶
        yoneda.obj U)
      (q : (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj W ⟶
        (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj V),
      IsPullback p' (yoneda.map q) f g := by
  let T := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let V' : AlgebraicGeometry.BigFppfOver B S hS :=
    (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj V
  have hVaff : IsAffine (T.obj V') :=
    AlgebraicGeometry.BigAffineFppf.isAffine_toScheme_obj B S hS V
  obtain ⟨W, hWcompact, ⟨e⟩⟩ :=
    ((AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_iff_compactSpace_pullback_affine
        B S hS hZ F hF).mp hqs)
      U V' f g hUaff hVaff
  let Vsp : AlgebraicSpaces B S hS :=
    ⟨yoneda.obj V', AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V'⟩
  let Usp : AlgebraicSpaces B S hS :=
    ⟨yoneda.obj U, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U⟩
  let Fsp : AlgebraicSpaces B S hS := ⟨F, hF⟩
  let gsp : Vsp ⟶ Fsp := ObjectProperty.homMk g
  let fsp : Usp ⟶ Fsp := ObjectProperty.homMk f
  let Psp := AlgebraicSpaces.fiberProduct B S hS fsp gsp
  have hPsp := AlgebraicGeometry.AlgebraicSpaces.isPullback_fiberProduct B S hS fsp gsp
  let toU : Psp ⟶ Usp := ObjectProperty.homMk (pullback.fst f g)
  let toV : Psp ⟶ Vsp := ObjectProperty.homMk (pullback.snd f g)
  have hEtaleP : AlgebraicGeometry.Space.IsEtale B S hS toU.hom :=
    AlgebraicGeometry.Space.isEtale_of_isPullback B S hS toV toU gsp fsp hPsp.flip hg
  let q : W ⟶ U := yoneda.preimage (e.hom ≫ toU.hom)
  let r : W ⟶ V' := yoneda.preimage (e.hom ≫ toV.hom)
  let Q := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) T
  have hIsoEtale : Q.presheaf e.hom := by
    refine ⟨yoneda.relativelyRepresentable.of_isIso e.hom, ?_⟩
    intro X Y k fst snd hsq
    have : IsIso (yoneda.map snd) := hsq.isIso_snd_of_isIso
    have : IsIso snd := Yoneda.fullyFaithful.isIso_of_isIso_map snd
    show Etale (T.map snd)
    infer_instance
  have hq : yoneda.map q = e.hom ≫ toU.hom := by simp [q]
  have hMapEtale : Q.presheaf (yoneda.map q) := by
    rw [hq]
    exact hEtaleP W e.hom hIsoEtale
  have : Etale (T.map q) :=
    (hMapEtale.2 (g := 𝟙 (yoneda.obj U)) (fst := 𝟙 (yoneda.obj W)) q IsPullback.of_id_fst : Q q)
  obtain ⟨-, hWaff, -⟩ := isFiniteLocallyFree_isAffine_of_etale_of_compactSpace (T.map q) hWcompact
  have hr : yoneda.map r = e.hom ≫ toV.hom := by simp [r]
  refine ⟨⟨W, hWaff⟩, e.hom ≫ pullback.fst f g, r, ?_⟩
  refine IsPullback.of_iso_pullback
    (fst := e.hom ≫ pullback.fst f g) (snd := yoneda.map r) (f := f) (g := g)
    ⟨?_⟩ e rfl (by rw [hr]; rfl)
  rw [hr]
  show (e.hom ≫ pullback.fst f g) ≫ f = (e.hom ≫ pullback.snd f g) ≫ g
  simp [pullback.condition]

/-- **Stacks 09TF, for an affine locally Artinian object of the site.**  A morphism from an
object of the big fppf site whose underlying scheme is affine and locally Artinian — the
spectrum of an Artinian ring — to a quasi-separated algebraic space is affine.

`AlgebraicGeometry.Space.isAffineHom_of_isArtinianRing` is the case of an object of the form
`Spec A ⟶ S`; the proof is the same.  For an étale morphism `V ⟶ X` from an affine object, the
fibre product with the source is quasi-compact because `X` is quasi-separated, and étale over
the source, so it is finite over it by
`AlgebraicGeometry.Space.isFinite_isLocallyArtinian_of_etale_of_quasiCompact`, hence affine. -/
theorem isAffineHom_of_isLocallyArtinian (hZ : B.Contains (⊤_ Scheme.{u}))
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ F) (U : BigFppfOver B S hS)
    [hUaff : IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    [IsLocallyArtinian ((BigFppfOver.toScheme B S hS).obj U)]
    (f : yoneda.obj U ⟶ F) : IsAffineHom B S hS f :=
  ((AlgebraicGeometry.Space.isAffineHom_tfae_of_isAlgebraicSpace B S hS f
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U) hF).out 3 2).mp
    (exists_isPullback_affine_of_isLocallyArtinian B S hS hZ hF hqs U f)

end AlgebraicGeometry.Space

end
