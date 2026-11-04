module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowup
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.Smallness
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenFiltrationSeparatedNeighbourhoods
import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackComponents
import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierPullbackCriteria
import StacksFrontier.AlgebraicGeometry.Stacks.EtaleOpenImmersion

/-!
# Extending an admissible blowup from a quasi-compact open subspace

Let `S` be a scheme, let `X` be a quasi-compact and quasi-separated algebraic space over `S` and
let `U, V ⊆ X` be quasi-compact open subspaces.  Tag 086D asserts that every `U ∩ V`-admissible
blowup `b : V' ⟶ V` is the restriction to `V` of a `U`-admissible blowup `X' ⟶ X`.

A `U`-admissible blowup is Tag 086B,
`AlgebraicGeometry.Space.IsAdmissibleBlowup`: a morphism `f : X' ⟶ X` for which there is a
closed subspace `Z ⊆ X` whose closed immersion into `X` is of finite presentation and whose
points are disjoint from those of `U`, such that `f` exhibits `X'` as the blowup of `X` in `Z`.
Equivalently, in the ideal-theoretic phrasing used by the source's proof, `f` is the blowup of
`X` in a finite type quasi-coherent ideal `𝓘 ⊆ 𝒪_X` whose vanishing locus is disjoint from `U`;
the restriction of such an ideal to `U` is the unit ideal `𝒪_U`.

## The source's proof, and which of its steps are available here

The source argues in three steps.  On `V` choose the finite type quasi-coherent ideal `𝓘` whose
blowup is `V'` and whose vanishing locus avoids `U ∩ V`; form the ideal on `U ∪ V` restricting
to `𝒪_U` on `U` and to `𝓘` on `V`; and extend that, by Tag 0853, to a finite type
quasi-coherent ideal `𝒥 ⊆ 𝒪_X`.  The blowup of `X` in `𝒥` is then `U`-admissible, because the
vanishing locus of `𝒥` meets `U` in the vanishing locus of the unit ideal, and its restriction
to `V` is the blowup of `V` in `𝓘`, which is `V'`.

The last of those three steps is the content of
`AlgebraicGeometry.Space.IsBlowupAlong.exists_restrictionToOpen` below and is proved here
unconditionally, from the universal property of Tag 085U alone; it carries
`@[stacks 086D "…"]` naming that clause.  The first two are the passage from `𝓘` to `𝒥`, by
Tag 0853, and the existence of the blowup of `X` in a finitely presented closed subspace is
Tag 085Q.  The full statement, with both of those proved, is
`AlgebraicGeometry.Space.exists_isAdmissibleBlowup_isPullback'` in
`StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupExtensionFromOpen`.  See the module
documentation of `StacksFrontier/AlgebraicGeometry/Spaces/AdmissibleBlowup.lean` for why the blowup
of an algebraic space can only be named by its universal property here.

## Main results

* `AlgebraicGeometry.Space.IsBlowupAlong.of_isPullback_of_isFlat`: a blowup stays a blowup under
  a flat base change, the centre being replaced by its inverse image.
* `AlgebraicGeometry.Space.IsBlowupAlong.exists_restrictionToOpen`: the blowup of `X` in `Z`
  restricts, over an open subspace `V ⊆ X`, to the blowup of `V` in `Z ∩ V`.

## Implementation notes

The inverse image `f⁻¹(V) ⊆ X'` of an open subspace is a cartesian square over `V ⊆ X` by Tag
083Q, `CategoryTheory.Subfunctor.isPullback_preimage`, so no fibre product has to be chosen to
name the restriction of `f` to `V`; the conclusion of
`AlgebraicGeometry.Space.exists_isAdmissibleBlowup_isPullback'` nevertheless says that the square
is cartesian, which is the source's "whose restriction to `V` is `V'`" and the shape
of the scheme-level Tag 080M, `Stacks.Blowup.exists_admissibleBlowup_isPullback`.

The inverse image of the centre stays an effective Cartier divisor because the inclusion of an
open subspace is étale, hence flat, and Stacks 083Z (2) applies.

## References

* [Stacks Project, Tag 086D](https://stacks.math.columbia.edu/tag/086D)
* [Stacks Project, Tag 086B](https://stacks.math.columbia.edu/tag/086B)
* [Stacks Project, Tag 085U](https://stacks.math.columbia.edu/tag/085U)
* [Stacks Project, Tag 085Q](https://stacks.math.columbia.edu/tag/085Q)
* [Stacks Project, Tag 0853](https://stacks.math.columbia.edu/tag/0853)
* [Stacks Project, Tag 083Z](https://stacks.math.columbia.edu/tag/083Z)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Restriction of subspaces to an open subspace -/

section Restriction

variable (X : AlgebraicSpaces B S hS)

/-- An open subspace of an algebraic space, as an algebraic space over `S` in its own right. -/
abbrev openSubspace (V : OpenSubspaces B S hS X.1) : AlgebraicSpaces B S hS :=
  ⟨V.1.toFunctor, V.2.1⟩

/-- The open immersion of an open subspace into the ambient algebraic space. -/
abbrev openSubspaceι (V : OpenSubspaces B S hS X.1) : openSubspace B S hS X V ⟶ X :=
  ObjectProperty.homMk V.1.ι

/-- The intersection `U ∩ V` of two open subspaces of `X`, as an open subspace of `V`: the
inverse image of `U` along the inclusion of `V`. -/
abbrev openSubspaceRestrict (V U : OpenSubspaces B S hS X.1) :
    OpenSubspaces B S hS (openSubspace B S hS X V).1 :=
  ⟨U.1.preimage V.1.ι, isOpenSubspace_preimage B S hS V.1.ι U.1 X.2 V.2.1 U.2⟩

/-- The scheme-theoretic intersection `Z ∩ V` of a closed subspace with an open subspace of `X`,
as a closed subspace of `V`: the inverse image of `Z` along the inclusion of `V`. -/
abbrev closedSubspaceRestrict (V : OpenSubspaces B S hS X.1)
    (Z : ClosedSubspaces B S hS X.1) : ClosedSubspaces B S hS (openSubspace B S hS X V).1 :=
  ⟨Z.1.preimage V.1.ι, isClosedSubspace_preimage B S hS V.1.ι Z.1 X.2 V.2.1 Z.2⟩

end Restriction

variable {B S hS}

/-- Being an effective Cartier divisor depends only on the underlying subfunctor of the closed
subspace. -/
theorem isEffectiveCartierDivisor_congr {X : AlgebraicSpaces B S hS}
    {Z W : ClosedSubspaces B S hS X.1} (h : Z.1 = W.1)
    (hZ : IsEffectiveCartierDivisor B S hS X Z) : IsEffectiveCartierDivisor B S hS X W :=
  Subtype.ext h ▸ hZ

/-- A closed subspace disjoint from an open subspace `U ⊆ X` restricts, on a second open
subspace `V ⊆ X`, to a closed subspace disjoint from `U ∩ V`: the points of `Z ∩ V` and of
`U ∩ V` are the inverse images of those of `Z` and of `U` under `|V| → |X|`. -/
theorem disjoint_subspacePointSet_closedSubspaceRestrict {X : AlgebraicSpaces B S hS}
    (U V : OpenSubspaces B S hS X.1) (Z : ClosedSubspaces B S hS X.1)
    (h : Disjoint (subspacePointSet B S hS X.1 U.1)
      (subspacePointSet B S hS X.1 Z.1)) :
    Disjoint (subspacePointSet B S hS (openSubspace B S hS X V).1
        (openSubspaceRestrict B S hS X V U).1)
      (subspacePointSet B S hS (openSubspace B S hS X V).1
        (closedSubspaceRestrict B S hS X V Z).1) := by
  rw [show (openSubspaceRestrict B S hS X V U).1 = U.1.preimage V.1.ι from rfl,
    show (closedSubspaceRestrict B S hS X V Z).1 = Z.1.preimage V.1.ι from rfl,
    subspacePointSet_preimage, subspacePointSet_preimage]
  exact h.preimage _

/-! ### Base change of a blowup -/

/-- **A blowup stays a blowup under a flat base change.**  Let `f : X' ⟶ X` be the blowup of `X`
in a closed subspace `Z ⊆ X`, let `g : Y ⟶ X` be a morphism of algebraic spaces and let the
square with projections `p : P ⟶ Y` and `q : P ⟶ X'` exhibit `P` as `Y ×_X X'`.  If `q` is flat
then `p` is the blowup of `Y` in the inverse image of `Z` in `Y`.

Both halves of the universal property of Tag 085U come out of the cartesian square.  The inverse
image of `Z` in `P` is the inverse image along `q` of the exceptional divisor of `f`, so it is an
effective Cartier divisor by Stacks 083Z (2), and `p` is an object of the category `𝒞` of Tag
085U for the centre `Z ×_X Y`.  An object `T ⟶ Y` of that category is, through `g`, an object of
the category for the centre `Z`, because the inverse image of `Z ×_X Y` in `T` is the inverse
image of `Z`; terminality of `f` carries it to `X'` over `X`, and the cartesian square carries
that uniquely to `P` over `Y`. -/
theorem IsBlowupAlong.of_isPullback_of_isFlat {X X' Y P : AlgebraicSpaces B S hS}
    {g : Y ⟶ X} {f : X' ⟶ X} {p : P ⟶ Y} {q : P ⟶ X'} (hsq : IsPullback p q g f)
    (hq : IsFlat B S hS q.hom) (Z : ClosedSubspaces B S hS X.1)
    (ZY : ClosedSubspaces B S hS Y.1) (hZY : ZY.1 = Z.1.preimage g.hom)
    (hf : IsBlowupAlong B S hS Z f) : IsBlowupAlong B S hS ZY p := by
  obtain ⟨hfmem, ⟨tf⟩⟩ := hf
  have hfD : IsEffectiveCartierDivisor B S hS X'
      ⟨Z.1.preimage f.hom, isClosedSubspace_preimage B S hS f.hom Z.1 X.2 X'.2 Z.2⟩ := hfmem
  have hw : q.hom ≫ f.hom = p.hom ≫ g.hom :=
    congrArg (fun m : P ⟶ X => m.hom) hsq.w.symm
  have hmemeq : (Z.1.preimage f.hom).preimage q.hom = ZY.1.preimage p.hom := by
    rw [hZY, ← Subfunctor.preimage_comp, ← Subfunctor.preimage_comp, hw]
  have hmem : IsCartierOver B S hS ZY (Over.mk p) :=
    isEffectiveCartierDivisor_congr hmemeq
      (isPullbackDefined_of_isFlat B S hS q _ hfD hq)
  let hover (T : CartierOver B S hS ZY) : CartierOver B S hS Z :=
    ⟨Over.mk (T.obj.hom ≫ g), isEffectiveCartierDivisor_congr
      (show ZY.1.preimage T.obj.hom.hom = Z.1.preimage (T.obj.hom.hom ≫ g.hom) by
        rw [hZY, Subfunctor.preimage_comp]) T.property⟩
  have key : ∀ T : CartierOver B S hS ZY, ∃ l : T.obj.left ⟶ P,
      l ≫ p = T.obj.hom ∧ ∀ l' : T.obj.left ⟶ P, l' ≫ p = T.obj.hom → l' = l := by
    intro T
    refine ⟨hsq.lift T.obj.hom (tf.from (hover T)).hom.left
      (Over.w (tf.from (hover T)).hom).symm, hsq.lift_fst _ _ _, fun l' hl' => ?_⟩
    have hcomm : (l' ≫ q) ≫ f = T.obj.hom ≫ g := by
      rw [Category.assoc, ← hsq.w, ← Category.assoc, hl']
    have hm : (ObjectProperty.homMk (Over.homMk (l' ≫ q) hcomm :
        Over.mk (T.obj.hom ≫ g) ⟶ Over.mk f) :
          hover T ⟶ ⟨Over.mk f, hfmem⟩) = tf.from _ := tf.hom_ext _ _
    refine hsq.hom_ext ?_ ?_
    · rw [hsq.lift_fst, hl']
    · rw [hsq.lift_snd]
      exact congrArg (fun k => k.hom.left) hm
  refine ⟨hmem, ⟨IsTerminal.ofUniqueHom
    (fun T => ObjectProperty.homMk (Over.homMk (key T).choose (key T).choose_spec.1))
    fun T m => ?_⟩⟩
  exact (ObjectProperty.ι (IsCartierOver B S hS ZY)).map_injective
    (Over.OverMorphism.ext ((key T).choose_spec.2 m.hom.left (Over.w m.hom)))

/-- **The blowup of `X` in a closed subspace `Z` restricts, over an open subspace `V ⊆ X`, to
the blowup of `V` in `Z ∩ V`.**  This is the clause "whose restriction to `V` is `V'`" of Tag
086D, and the one step of its proof that the universal property of Tag 085U supplies on its own.

The inverse image `f⁻¹(V)` is an open subspace of `X'` and exhibits a cartesian square over
`V ⊆ X` by Tag 083Q; the inclusion of an open subspace is étale, hence flat, so
`AlgebraicGeometry.Space.IsBlowupAlong.of_isPullback_of_isFlat` applies. -/
@[stacks 086D "unconditional: the restriction over an open subspace `V` of the blowup of `X` in \
`Z` is the blowup of `V` in `Z ∩ V`"]
theorem IsBlowupAlong.exists_restrictionToOpen {X X' : AlgebraicSpaces B S hS} {f : X' ⟶ X}
    (V : OpenSubspaces B S hS X.1) (Z : ClosedSubspaces B S hS X.1)
    (hf : IsBlowupAlong B S hS Z f) :
    ∃ (P : AlgebraicSpaces B S hS) (p : P ⟶ openSubspace B S hS X V) (q : P ⟶ X'),
      IsPullback p q (openSubspaceι B S hS X V) f ∧
        IsBlowupAlong B S hS (closedSubspaceRestrict B S hS X V Z) p := by
  have hW : IsOpenSubspace B S hS (V.1.preimage f.hom) :=
    isOpenSubspace_preimage B S hS f.hom V.1 X.2 X'.2 V.2
  have hsq : IsPullback
      (ObjectProperty.homMk (V.1.fromPreimage f.hom) :
        (⟨(V.1.preimage f.hom).toFunctor, hW.1⟩ : AlgebraicSpaces B S hS) ⟶
          openSubspace B S hS X V)
      (ObjectProperty.homMk (V.1.preimage f.hom).ι) (openSubspaceι B S hS X V) f :=
    IsPullback.of_map_of_faithful
      (ObjectProperty.ι (fun T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS T))
      (Subfunctor.isPullback_preimage f.hom V.1)
  exact ⟨_, _, _, hsq, IsBlowupAlong.of_isPullback_of_isFlat hsq
    (isFlat_of_isEtale B S hS (isEtale_of_isOpenImmersion B S hS hW.2)) Z _ rfl hf⟩

end AlgebraicGeometry.Space

end
