module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.UniversalExistence.Construction
import all StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.UniversalExistence.FirstOrderClauseAndAffineSize
import all StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.UniversalExistence.SiteThickening
import all StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.UniversalExistence.Construction

/-!
# Universal thickening existence: existence and transport

The universal first order thickening of a morphism of the site inside the site, the transport of
the scheme-level universal property along an isomorphism of thickenings, and **Stacks 0606**, the
existence of the universal first order thickening of a formally unramified morphism of algebraic
spaces.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Spaces.UniversalThickening

open AlgebraicGeometry.Space

/-- **A morphism of the site whose underlying morphism of schemes is formally unramified has a
universal first-order thickening inside the site.**  The scheme-level universal first-order
thickening of Stacks 04F3 satisfies the size bound of the site, so it is the underlying scheme of
an object of the site, through which the morphism factors. -/
theorem exists_site_universalFirstOrderThickening
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {V U : AlgebraicGeometry.BigFppfOver B S hS} (q : V ⟶ U)
    [AlgebraicGeometry.FormallyUnramified ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map q)] :
    ∃ (V' : AlgebraicGeometry.BigFppfOver B S hS) (i : V ⟶ V') (p : V' ⟶ U), i ≫ p = q ∧
      Stacks.Thickenings.IsUniversalFirstOrderThickening
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map q)
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map i)
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map p) := by
  let F := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let t := Stacks.Thickenings.universalFirstOrderThickening (F.map q)
  have ht : B.Contains t.ambient :=
    contains_ambient_of_isUniversalFirstOrderThickening B V.left.property U.left.property (F.map q)
      t.inclusion t.toBase t.isUniversal
  let V' : AlgebraicGeometry.BigFppfOver B S hS :=
    Over.mk (ObjectProperty.homMk (t.toBase ≫ U.hom.hom) : B.obj ht ⟶ B.obj hS)
  have hiS : t.inclusion ≫ (t.toBase ≫ U.hom.hom) = V.hom.hom := by
    rw [← Category.assoc, t.isUniversal.inclusion_toBase]
    exact congrArg (fun f => f.hom) q.w
  let i : V ⟶ V' := Over.homMk (ObjectProperty.homMk t.inclusion)
    (by apply ObjectProperty.hom_ext; exact hiS)
  let p : V' ⟶ U := Over.homMk (ObjectProperty.homMk t.toBase) rfl
  have hcomp : i ≫ p = q := F.map_injective t.isUniversal.inclusion_toBase
  exact ⟨V', i, p, hcomp, t.isUniversal⟩

/-! ### Transport of the scheme-level universal property along an isomorphism

The crossing from the spaces-level universal property to the scheme-level one cannot be a
restriction of the quantifier — the two are incomparable, as the roadmap note of
`StacksFrontier/AlgebraicGeometry/Spaces/UniversalThickeningComposition.lean` records — so it has
to be made the way the existence theorem below is made: produce the scheme-level thickening
from Stacks 04F3, keep its ambient inside the site by the cardinal arithmetic above, cross to
the spaces level in the direction already proved, identify the two spaces-level thickenings by the
uniqueness clause of Stacks 0602 (`universalThickening_iso` above), and transport the
scheme-level property back along the resulting isomorphism.  The four steps are this section.

`Stacks.Thickenings.UniversalFirstOrderThickening.canonicalIso` of
`StacksFrontier/AlgebraicGeometry/Thickenings/UniversalConormal.lean` is **not** the last step and
does not subsume it: it compares two thickenings of one morphism which *both already have* the
scheme-level universal property, whereas what is wanted here is to move that property to a
scheme which does not yet have it, along an isomorphism that comes from somewhere else — the
spaces level. -/

/-- **The scheme-level universal property is invariant under an isomorphism of the ambient
scheme.**  If `Z ⊂ Z'` is a universal first-order thickening of `Z` over `X` and `e : Z' ≅ Z''`
carries its inclusion and its structure morphism to `i''` and `h''`, then `Z ⊂ Z''` is one too.

The lifting clause is conjugation by `e`: a lift into `Z''` is a lift into `Z'` followed by
`e.hom`, and `e` being an isomorphism that is a bijection respecting both equations, so the
`ExistsUnique` transports term for term.

The square-zero clause is an input rather than a conclusion, deliberately.  Transporting it
would mean moving `AlgebraicGeometry.Scheme.Hom.ker` — an ideal sheaf on the *target* — across
`e`, for which Mathlib's `AlgebraicGeometry.Scheme.Hom.ker_comp_of_isIso` is the wrong side: it
cancels an isomorphism on the left, not on the right.  Every consumer of this lemma arrives
with the clause for `i''` already, so asking for it costs nothing and keeps the ideal-sheaf
transport out of the way.

**Where the crossing that would consume this still stops.**  Assembling the route above into a
converse of `AlgebraicGeometry.Space.isUniversalFirstOrderThickening_range_yoneda_map` — from
`Stacks.Thickenings.nonempty_universalFirstOrderThickening`, through
`AlgebraicGeometry.Space.contains_ambient_of_isUniversalFirstOrderThickening`,
`exists_site_universalThickening` and
`universalThickening_iso`, to this lemma — **exhausts the heartbeat budget**:
`(deterministic) timeout at whnf` at 200,000, reported at the declaration.  Two candidate causes
are ruled out.  It is not `CategoryTheory.Iso.trans_hom` failing to fire, and not
the `change`s needed to read an `Iso.trans`'s or a `CategoryTheory.Functor.mapIso`'s `hom` as a
composite: building both isomorphisms by hand with `CategoryTheory.Iso.mk`, so that every
projection is syntactic, and normalising `(AlgebraicGeometry.schemeSpaceMap _).hom` with
`AlgebraicGeometry.schemeSpaceMap_hom` instead, changes the cost not at all.  What remains as the
candidate is the `subst` of the ambient-scheme equality that `exists_site_universalThickening`
returns, carried through a context holding the universal property, together with the two `HEq`s
beside it.

The concrete repair is to that lemma rather than to its consumers.  Its proof already constructs
`Stacks.Thickenings.IsUniversalFirstOrderThickening (F.map (i ≫ p)) (F.map i) (F.map p)` — the
local `hu` — and then discards it, returning instead the ambient-scheme equality and two `HEq`s
from which every consumer has to rebuild it.  Returning `hu` as a further conjunct of its
existential would remove the `subst` and both `HEq`s from the crossing, and from any other
consumer, at no cost to its own proof. -/
public lemma isUniversalFirstOrderThickening_of_iso
    {Z X Z' Z'' : Scheme.{u}} {h : Z ⟶ X} {i : Z ⟶ Z'} {h' : Z' ⟶ X}
    {i'' : Z ⟶ Z''} {h'' : Z'' ⟶ X}
    (hu : Stacks.Thickenings.IsUniversalFirstOrderThickening h i h')
    (hfo : Stacks.Thickenings.IsFirstOrderThickening i'')
    (e : Z' ≅ Z'') (hi : i ≫ e.hom = i'') (hb : e.hom ≫ h'' = h') :
    Stacks.Thickenings.IsUniversalFirstOrderThickening h i'' h'' where
  isFirstOrderThickening := hfo
  inclusion_toBase := by
    rw [← hi, Category.assoc, hb]
    exact hu.inclusion_toBase
  existsUnique_lift := by
    intro T T' j hj a b hab
    obtain ⟨c, hc, hcu⟩ := hu.existsUnique_lift j hj a b hab
    refine ⟨c ≫ e.hom, ⟨?_, ?_⟩, ?_⟩
    · rw [← Category.assoc, hc.1, ← hi, Category.assoc]
    · rw [Category.assoc, hb]
      exact hc.2
    · intro d hd
      have hde : d ≫ e.inv = c := by
        refine hcu (d ≫ e.inv) ⟨?_, ?_⟩
        · rw [← Category.assoc, hd.1, ← hi]
          simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
        · rw [Category.assoc, ← hb, e.inv_hom_id_assoc]
          exact hd.2
      rw [← hde, Category.assoc, e.inv_hom_id, Category.comp_id]

/-- **The Yoneda image of a morphism of the site that is a first-order thickening of schemes is a
monomorphism.** -/
private lemma mono_yoneda_map_of_isFirstOrderThickening
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {W V : AlgebraicGeometry.BigFppfOver B S hS} (i : W ⟶ V)
    (hfo : Stacks.Thickenings.IsFirstOrderThickening
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map i)) :
    Mono (yoneda.map i) := by
  have : IsClosedImmersion ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map i) := hfo.1
  have : Mono i := (AlgebraicGeometry.BigFppfOver.toScheme B S hS).mono_of_mono_map
    (inferInstanceAs (Mono ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map i)))
  infer_instance

/-- **Uniqueness of represented universal first-order thickenings, as an isomorphism of the
site.**  Two thickenings `W ⟶ V' ⟶ U` and `W ⟶ V₀ ⟶ U` of the big fppf category over `S`, each
a first-order thickening of schemes and each representing a spaces-level universal first-order
thickening of `W` over `U`, are isomorphic over `U` and under `W` by a unique isomorphism of the
site.

It is `universalThickening_iso`, the uniqueness clause of Stacks 0602, at the two ranges of the
Yoneda images, each identified with `yoneda.obj W` through `CategoryTheory.Subfunctor.toRange`,
followed by the descent of the resulting isomorphism of representables to the site along the
full faithfulness of the Yoneda embedding. -/
public lemma exists_site_iso_of_universalThickenings
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {W V' V₀ U : AlgebraicGeometry.BigFppfOver B S hS} (i : W ⟶ V') (p : V' ⟶ U)
    (i₀ : W ⟶ V₀) (p₀ : V₀ ⟶ U) (hcomp₀ : i₀ ≫ p₀ = i ≫ p)
    (hfo : Stacks.Thickenings.IsFirstOrderThickening
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map i))
    (hfo₀ : Stacks.Thickenings.IsFirstOrderThickening
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map i₀))
    (h : AlgebraicGeometry.Space.IsUniversalFirstOrderThickening B S hS
      (Subfunctor.range (yoneda.map i)) (AlgebraicGeometry.schemeSpaceMap p))
    (hsp₀ : AlgebraicGeometry.Space.IsUniversalFirstOrderThickening B S hS
      (Subfunctor.range (yoneda.map i₀)) (AlgebraicGeometry.schemeSpaceMap p₀)) :
    ∃ g : V' ⟶ V₀, IsIso g ∧ i ≫ g = i₀ ∧ g ≫ p₀ = p := by
  have : Mono (yoneda.map i) := mono_yoneda_map_of_isFirstOrderThickening B S hS i hfo
  have : Mono (yoneda.map i₀) := mono_yoneda_map_of_isFirstOrderThickening B S hS i₀ hfo₀
  let eZ : yoneda.obj W ≅ (Subfunctor.range (yoneda.map i)).toFunctor :=
    asIso (Subfunctor.toRange (yoneda.map i))
  let eY : yoneda.obj W ≅ (Subfunctor.range (yoneda.map i₀)).toFunctor :=
    asIso (Subfunctor.toRange (yoneda.map i₀))
  have hZ' : eZ.hom ≫ (Subfunctor.range (yoneda.map i)).ι = yoneda.map i :=
    Subfunctor.toRange_ι (yoneda.map i)
  have hY' : eY.hom ≫ (Subfunctor.range (yoneda.map i₀)).ι = yoneda.map i₀ :=
    Subfunctor.toRange_ι (yoneda.map i₀)
  have hZi : eZ.inv ≫ yoneda.map i = (Subfunctor.range (yoneda.map i)).ι :=
    (congrArg (fun t => eZ.inv ≫ t) hZ'.symm).trans (eZ.inv_hom_id_assoc _)
  let e : (Subfunctor.range (yoneda.map i)).toFunctor ≅
      (Subfunctor.range (yoneda.map i₀)).toFunctor :=
    { hom := eZ.inv ≫ eY.hom
      inv := eY.inv ≫ eZ.hom
      hom_inv_id := by rw [Category.assoc, eY.hom_inv_id_assoc, eZ.inv_hom_id]
      inv_hom_id := by rw [Category.assoc, eZ.hom_inv_id_assoc, eY.inv_hom_id] }
  have hsq : (Subfunctor.range (yoneda.map i)).ι ≫
        (AlgebraicGeometry.schemeSpaceMap p).hom =
      e.hom ≫ (Subfunctor.range (yoneda.map i₀)).ι ≫
        (AlgebraicGeometry.schemeSpaceMap p₀).hom := by
    simp only [AlgebraicGeometry.schemeSpaceMap_hom]
    change (Subfunctor.range (yoneda.map i)).ι ≫ yoneda.map p =
      (eZ.inv ≫ eY.hom) ≫ (Subfunctor.range (yoneda.map i₀)).ι ≫ yoneda.map p₀
    rw [Category.assoc, ← Category.assoc eY.hom, hY', ← yoneda.map_comp, hcomp₀,
      yoneda.map_comp, ← Category.assoc, hZi]
  -- Every implicit is supplied.  Left to unification, checking `hsq` against the expected type
  -- exhausts the heartbeat budget at `whnf`.
  obtain ⟨e', hA, hB⟩ := universalThickening_iso B S hS
    (X := AlgebraicGeometry.schemeSpace U) (Y' := AlgebraicGeometry.schemeSpace V₀)
    (Z' := AlgebraicGeometry.schemeSpace V')
    (Subfunctor.range (yoneda.map i₀)) (Subfunctor.range (yoneda.map i))
    (AlgebraicGeometry.schemeSpaceMap p₀) (AlgebraicGeometry.schemeSpaceMap p)
    hsp₀ h e hsq
  -- `hA` is restated once, at the spelling the rest of this proof uses.  Its own sides are
  -- typed through `(AlgebraicGeometry.schemeSpace V').obj` and these through `yoneda.obj V'`;
  -- the two are equal by `AlgebraicGeometry.schemeSpace_obj`, hence by `rfl`, but not
  -- syntactically, so `rw` reports the pattern absent from a goal that displays it and `calc`
  -- cannot chain the steps for want of a `Trans` instance.  One ascription, with no
  -- metavariables left in it, settles the difference for the whole proof.
  have hA' : (Subfunctor.range (yoneda.map i)).ι ≫ e'.hom =
      e.hom ≫ (Subfunctor.range (yoneda.map i₀)).ι := hA
  have hmap : yoneda.map i ≫ e'.hom = yoneda.map i₀ := by
    have h3 : (eZ.hom ≫ (Subfunctor.range (yoneda.map i)).ι) ≫ e'.hom =
        eZ.hom ≫ e.hom ≫ (Subfunctor.range (yoneda.map i₀)).ι :=
      (Category.assoc _ _ _).trans (congrArg (fun t => eZ.hom ≫ t) hA')
    rw [hZ'] at h3
    refine h3.trans ?_
    change eZ.hom ≫ (eZ.inv ≫ eY.hom) ≫ (Subfunctor.range (yoneda.map i₀)).ι = yoneda.map i₀
    rw [Category.assoc, eZ.hom_inv_id_assoc, hY']
  have hbase : e'.hom ≫ yoneda.map p₀ = yoneda.map p := by
    have h2 := hB
    simp only [AlgebraicGeometry.schemeSpaceMap_hom] at h2
    exact h2
  have hg : yoneda.map (yoneda.preimage e'.hom) = e'.hom := yoneda.map_preimage e'.hom
  have : IsIso (yoneda.map (yoneda.preimage e'.hom)) := by
    rw [hg]
    exact ⟨e'.inv, e'.hom_inv_id, e'.inv_hom_id⟩
  refine ⟨yoneda.preimage e'.hom,
    Functor.FullyFaithful.isIso_of_isIso_map Yoneda.fullyFaithful _, ?_, ?_⟩
  · refine yoneda.map_injective ?_
    rw [yoneda.map_comp, hg]
    exact hmap
  · refine yoneda.map_injective ?_
    rw [yoneda.map_comp, hg]
    exact hbase

/-- **The transport half of the crossing**, isolated so that its cost is separate
from the half that produces the comparison.  Given a second thickening `W ⟶ V₀ ⟶ U` of the site
which already carries the scheme-level universal property, and an isomorphism `g : V' ⟶ V₀` of
the site carrying `i` to `i₀` and `p₀` back to `p`, the given `W ⟶ V'` carries it too.

It is `isUniversalFirstOrderThickening_of_iso` at the image of `g` under
`AlgebraicGeometry.BigFppfOver.toScheme`, with that isomorphism built by hand so that its `hom`
is `F.map (inv g)` on the nose rather than a `CategoryTheory.Functor.mapIso`. -/
public lemma isUniversalFirstOrderThickening_map_of_site_iso
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {W V' V₀ U : AlgebraicGeometry.BigFppfOver B S hS} (i : W ⟶ V') (p : V' ⟶ U)
    {i₀ : W ⟶ V₀} {p₀ : V₀ ⟶ U} (g : V' ⟶ V₀) [IsIso g]
    (hig : i ≫ g = i₀) (hpg : g ≫ p₀ = p)
    (hu₀ : Stacks.Thickenings.IsUniversalFirstOrderThickening
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (i ≫ p))
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map i₀)
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map p₀))
    (hfo : Stacks.Thickenings.IsFirstOrderThickening
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map i)) :
    Stacks.Thickenings.IsUniversalFirstOrderThickening
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (i ≫ p))
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map i)
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map p) := by
  let eS : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj V₀ ≅
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj V' :=
    { hom := (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (inv g)
      inv := (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g
      hom_inv_id := by
        rw [← (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map_comp, IsIso.inv_hom_id,
          (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map_id]
      inv_hom_id := by
        rw [← (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map_comp, IsIso.hom_inv_id,
          (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map_id] }
  refine isUniversalFirstOrderThickening_of_iso hu₀ hfo eS ?_ ?_
  · change (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map i₀ ≫
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (inv g) =
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map i
    rw [← (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map_comp, ← hig, Category.assoc,
      IsIso.hom_inv_id, Category.comp_id]
  · change (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (inv g) ≫
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map p =
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map p₀
    rw [← (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map_comp, ← hpg,
      IsIso.inv_hom_id_assoc]

/-- **The crossing: a spaces-level universal first-order thickening of represented spaces is a
scheme-level one.**  Let `i : W ⟶ V'` and `p : V' ⟶ U` be morphisms of the big fppf category
over `S` whose underlying `W ⟶ U` is formally unramified, let `W ⟶ V'` be a first-order
thickening of schemes, and suppose the range of `yoneda.map i` is a universal first-order
thickening of the algebraic space represented by `W` over the one represented by `U`.  Then
`W ⟶ V'` is a universal first-order thickening of `W` over `U` *as schemes*.

This is the converse of
`AlgebraicGeometry.Space.isUniversalFirstOrderThickening_range_yoneda_map`, and it is **not** a
restriction of the quantifier.  The two universal properties are incomparable: the spaces-level
one tests arbitrary algebraic spaces over `S`, so it is wider in generality, but every object of
`AlgebraicGeometry.BigFppfOver B S hS` satisfies `AlgebraicGeometry.BigFppfSite.Contains`, which
is literally `T.size < B.cutoff`, while the scheme-level `existsUnique_lift` quantifies over
`Scheme.{u}` with no bound at all, so it is wider in size.  Restricting to affine test objects
does not help, the criterion of Stacks 0603 still ranging over algebraic spaces.  The roadmap
note of `StacksFrontier/AlgebraicGeometry/Spaces/UniversalThickeningComposition.lean` sets this out.

The proof goes around instead, exactly as the existence theorem below does, and in four
steps: Stacks 04F3 produces a universal first-order thickening of `W ⟶ U` in schemes;
`AlgebraicGeometry.Space.contains_ambient_of_isUniversalFirstOrderThickening` keeps its ambient
scheme inside the site, by the cardinal
arithmetic of this file and with no affineness needed;
`exists_site_universalThickening_of_universalProperty` realises it as a morphism of the site
carrying both levels' properties at once; `exists_site_iso_of_universalThickenings` identifies it
with the given thickening by the uniqueness clause of Stacks 0602; and
`isUniversalFirstOrderThickening_map_of_site_iso` transports the scheme-level property back along
that isomorphism. -/
public lemma isUniversalFirstOrderThickening_map_of_range_yoneda_map
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {W V' U : AlgebraicGeometry.BigFppfOver B S hS} (i : W ⟶ V') (p : V' ⟶ U)
    [FormallyUnramified ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (i ≫ p))]
    (hfo : Stacks.Thickenings.IsFirstOrderThickening
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map i))
    (h : AlgebraicGeometry.Space.IsUniversalFirstOrderThickening B S hS
      (Subfunctor.range (yoneda.map i)) (AlgebraicGeometry.schemeSpaceMap p)) :
    Stacks.Thickenings.IsUniversalFirstOrderThickening
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (i ≫ p))
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map i)
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map p) := by
  classical
  obtain ⟨t⟩ := Stacks.Thickenings.nonempty_universalFirstOrderThickening
    ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (i ≫ p))
  have ht : B.Contains t.ambient :=
    contains_ambient_of_isUniversalFirstOrderThickening B W.left.property U.left.property
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (i ≫ p))
      t.inclusion t.toBase t.isUniversal
  obtain ⟨V₀, i₀, p₀, hcomp₀, hfo₀, hu₀, hsp₀⟩ :=
    exists_site_universalThickening_of_universalProperty B S hS (i ≫ p) t ht
  obtain ⟨g, hgiso, hig, hpg⟩ :=
    exists_site_iso_of_universalThickenings B S hS i p i₀ p₀ hcomp₀ hfo hfo₀ h hsp₀
  have := hgiso
  exact isUniversalFirstOrderThickening_map_of_site_iso B S hS i p g hig hpg hu₀ hfo

end Stacks.Spaces.UniversalThickening

namespace AlgebraicGeometry.Space

/-- **Stacks 0606.** Every formally unramified morphism `h : Z ⟶ X` of algebraic spaces over
`S` admits a universal first order thickening `Z ⊂ Z'` of `Z` over `X`, in the sense of
Stacks 0602. -/
@[stacks 0606]
theorem nonempty_universalFirstOrderThickening
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z X : AlgebraicGeometry.AlgebraicSpaces B S hS} (h : Z ⟶ X)
    (hh : FormallyUnramified h.hom) :
    Nonempty (UniversalFirstOrderThickening B S hS h) := by
  obtain ⟨t, hbase, huniv⟩ :=
    Stacks.Spaces.UniversalThickening.exists_universalFirstOrderThickening_with_spec
      B S hS h hh
  exact ⟨{ formallyUnramified := hh
           ambient := t.ambient
           toBase := t.toBase
           sub := t.source
           isUniversal := huniv
           sourceIso := t.sourceIso
           sourceIso_ι_toBase := hbase }⟩
end AlgebraicGeometry.Space

end
