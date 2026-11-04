module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Completion
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtale
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Types
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.InvariantSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Modifications
public import StacksFrontier.AlgebraicGeometry.Spaces.Smooth
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.OpenSubspaces
public import StacksFrontier.RingTheory.Restricted.RigSmoothSmoothLocus
public import StacksFrontier.RingTheory.Rig.RigEtaleLocus

/-!
# Rig-smoothness and rig-étaleness of a morphism of completions

Let `S` be a scheme contained in a big fppf site `B`, let `f : X' ⟶ X` be a morphism of
algebraic spaces over `S` and let `T` be a set of points of `X`. Write `T' = |f|⁻¹ T`, write
`U ⊂ X` for the open subspace with `|U| = |X| ∖ T` and `U' = f⁻¹U ⊂ X'` for the open subspace
with `|U'| = |X'| ∖ T'`; this is the situation of Stacks 0GDB, and the completion square
`X'_{/T'} → X' → X ← X_{/T}` is cartesian by Stacks 0APV.

**Stacks 0GDH** says that if `X` is locally Noetherian, `f` is locally of finite type and
`U' → U` is smooth, then `f_{/T}` is rig-smooth. **Stacks 0AR2** says the same with smooth
replaced by étale and rig-smooth by rig-étale.

## Main definitions

* `AlgebraicGeometry.Space.openComplementRestriction`: the morphism `U' ⟶ U` of the situation
  above.
* `AlgebraicGeometry.FormalSpace.ChartSquareReducesToSmoothAwayFrom` and
  `AlgebraicGeometry.FormalSpace.ChartSquareReducesToIsEtaleOutside`: the reduction to the
  affine case, which is the input this library does not carry, once for each of the two
  lemmas.

## Main results

* `AlgebraicGeometry.FormalSpace.isRigSmooth_completionSheafMap`: **Stacks 0GDH**.
* `AlgebraicGeometry.FormalSpace.isRigEtale_completionSheafMap`: **Stacks 0AR2**.

## Implementation notes

### The open complement and its restriction

`U` is `AlgebraicGeometry.Space.openSubspaceOfPoints` on `Tᶜ`, whose point set is `Tᶜ` by
Stacks 03BZ and which is an open subspace when `T` is closed. Since the inverse image of the
subspace cut out by a set of points is the one cut out by the preimage of that set
(`AlgebraicGeometry.Space.preimage_openSubspaceOfPoints`), the open subspace of `X'` cut out
by `|f|⁻¹ Tᶜ = (|f|⁻¹ T)ᶜ` *is* `f⁻¹U`, and the morphism `U' ⟶ U` is the universal map out of
that inverse image.

### The structure of the two proofs

Both lemmas are proved in the source by reducing to the case of affine schemes and then
translating the affine case into algebra, where it becomes Stacks 0GAK respectively Stacks
0ALQ. Those two ring-theoretic results are what this library carries:
`Rig.isRigSmooth_adicCompletionObj_of_smoothAwayFrom` is part (1) of Stacks 0GAK and
`Rig.isRigEtale_adicCompletionObj_of_isEtaleOutside` is part (1) of Stacks 0ALQ. They are the
only mathematical input of the proofs below.

The reduction is the hypothesis, once for each lemma. It takes the hypotheses of the lemma —
`f` locally of finite type and `U' → U` smooth, respectively étale — and produces, for each
affine representable étale square over `f_{/T}` presented by an arrow `g : A → C` of
`WAdm^{Noeth}`, the affine data the source's proof produces: a Noetherian ring `A₀`, an ideal
`I₀ ⊆ A₀` and a finite type `A₀`-algebra `C₀` with `Spec C₀ → Spec A₀` smooth, respectively
étale, over `Spec A₀ ∖ V(I₀)`, together with the comparison that turns rig-smoothness,
respectively rig-étaleness, of the `I₀`-adic completion `C₀^` over `(A₀, I₀)` into the
condition on `g`. The source builds that data from: Properties of Spaces, Lemma 03FX, for the
étale cover of `X` by affine schemes and of `X'` over it; the cartesian completion squares of
Stacks 0APV, which identify `(W_i)_{/T_i}` with `W_i ×_X X_{/T}`; the identification
`X_{/T} = Spf(A^∧)` of the proof of Stacks 0AQ1; and the fact that local finite type,
smoothness and étaleness of a morphism and local Noetherianity of an algebraic space are étale
local on source and target. None of these is carried here in the form the reduction needs,
which is why it is a hypothesis; and it is a statement about the charts of `f_{/T}` and the
rings presenting them, not the assertion of the lemma.

The hypothesis that `X` is locally Noetherian is read as local Noetherianity of every scheme
étale over `X`, which is the form Properties of Spaces, Definition 03E2 takes after Lemma
03FX; it is `AlgebraicGeometry.Space.IsLocallyNoetherian`.

## References

* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 03E2](https://stacks.math.columbia.edu/tag/03E2)
* [Stacks Project, Tag 03FX](https://stacks.math.columbia.edu/tag/03FX)
* [Stacks Project, Tag 0ALQ](https://stacks.math.columbia.edu/tag/0ALQ)
* [Stacks Project, Tag 0APV](https://stacks.math.columbia.edu/tag/0APV)
* [Stacks Project, Tag 0AQ1](https://stacks.math.columbia.edu/tag/0AQ1)
* [Stacks Project, Tag 0AR2](https://stacks.math.columbia.edu/tag/0AR2)
* [Stacks Project, Tag 0GAK](https://stacks.math.columbia.edu/tag/0GAK)
* [Stacks Project, Tag 0GDB](https://stacks.math.columbia.edu/tag/0GDB)
* [Stacks Project, Tag 0GDH](https://stacks.math.columbia.edu/tag/0GDH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### The open complement of a set of points and the restriction to it -/

/-- The morphism `U' ⟶ U` of the situation of **Stacks 0GDB**: the restriction of
`f : X' ⟶ X` to the open subspace `U ⊂ X` with `|U| = |X| ∖ T` and its inverse image
`U' = f⁻¹U ⊂ X'`, which is the open subspace with `|U'| = |X'| ∖ |f|⁻¹T`.

Both open subspaces are cut out by their sets of points, and `U'` is `f⁻¹U` because the
inverse image of the subspace cut out by a set of points is the one cut out by the preimage of
that set. -/
def openComplementRestriction (f : X' ⟶ X) (T : Set (points B S hS X)) :
    (openSubspaceOfPoints B S hS X' (pointsMap B S hS X' f ⁻¹' Tᶜ)).toFunctor ⟶
      (openSubspaceOfPoints B S hS X Tᶜ).toFunctor :=
  Subfunctor.lift ((openSubspaceOfPoints B S hS X' (pointsMap B S hS X' f ⁻¹' Tᶜ)).ι ≫ f) (by
    rw [Subfunctor.range_comp, Subfunctor.range_ι, Subfunctor.image_le_iff,
      preimage_openSubspaceOfPoints])

/-- The restriction to the open complements is the restriction of `f`: composing it with the
inclusion of `U` is the inclusion of `U'` followed by `f`. -/
theorem openComplementRestriction_ι (f : X' ⟶ X) (T : Set (points B S hS X)) :
    openComplementRestriction B S hS f T ≫ (openSubspaceOfPoints B S hS X Tᶜ).ι =
      (openSubspaceOfPoints B S hS X' (pointsMap B S hS X' f ⁻¹' Tᶜ)).ι ≫ f :=
  rfl

/-- The point set of `U'` is the complement of `T' = |f|⁻¹T`, so `U'` is the open subspace of
the situation of Stacks 0GDB. -/
theorem preimage_compl_points (f : X' ⟶ X) (T : Set (points B S hS X)) :
    pointsMap B S hS X' f ⁻¹' Tᶜ = (pointsMap B S hS X' f ⁻¹' T)ᶜ :=
  Set.preimage_compl

/-- For `T` closed, `U` is an open subspace of `X` with `|U| = |X| ∖ T`, by Stacks 03BZ. -/
theorem isOpenSubspace_openSubspaceOfPoints_compl_of_isClosed
    (hX : IsAlgebraicSpace B S hS X)
    (T : Set (points B S hS X)) (hT : IsClosed T) :
    IsOpenSubspace B S hS (openSubspaceOfPoints B S hS X Tᶜ) :=
  isOpenSubspace_openSubspaceOfPoints B S hS hX Tᶜ hT.isOpen_compl

/-- **Properties of Spaces, Definition 03E2** read through Lemma 03FX: an algebraic space over
`S` is *locally Noetherian* when every scheme étale over it is locally Noetherian. -/
abbrev IsLocallyNoetherian (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  ∀ (W : BigFppfOver B S hS) (q : yoneda.obj W ⟶ X), IsEtale B S hS q →
    _root_.AlgebraicGeometry.IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj W)

/-! ### `U'` is the fibre product of `U` with `f` -/

/-- `U' = f⁻¹U`: the square formed by the two open complements, `f` and the inclusion of `U`
is cartesian, because the inverse image of a subfunctor is its fibre product with the ambient
morphism and the inverse image of the subspace cut out by a set of points is the one cut out
by the preimage of that set. -/
theorem isPullback_openComplementRestriction (f : X' ⟶ X) (T : Set (points B S hS X)) :
    IsPullback (openSubspaceOfPoints B S hS X' (pointsMap B S hS X' f ⁻¹' Tᶜ)).ι
      (openComplementRestriction B S hS f T) f (openSubspaceOfPoints B S hS X Tᶜ).ι := by
  have key : ∀ V : Subfunctor X', V = (openSubspaceOfPoints B S hS X Tᶜ).preimage f →
      ∀ hle : Subfunctor.range (V.ι ≫ f) ≤ openSubspaceOfPoints B S hS X Tᶜ,
      IsPullback V.ι (Subfunctor.lift (V.ι ≫ f) hle) f
        (openSubspaceOfPoints B S hS X Tᶜ).ι := by
    rintro V rfl hle
    exact (Subfunctor.isPullback_fromPreimage (openSubspaceOfPoints B S hS X Tᶜ) f).flip
  exact key _ (preimage_openSubspaceOfPoints B S hS f Tᶜ).symm _

/-- If the base change of `f` to `U` is an isomorphism, then so is the restriction `U' ⟶ U`:
the latter is the former composed with the comparison isomorphism of the cartesian square
above. -/
theorem isIso_openComplementRestriction (f : X' ⟶ X) (T : Set (points B S hS X))
    (h : IsIso (pullback.snd f (openSubspaceOfPoints B S hS X Tᶜ).ι)) :
    IsIso (openComplementRestriction B S hS f T) := by
  have hsq := isPullback_openComplementRestriction B S hS f T
  have : IsIso (pullback.snd f (openSubspaceOfPoints B S hS X Tᶜ).ι) := h
  rw [← hsq.isoPullback_hom_snd]
  infer_instance

/-- If the base change of `f` to `U` is an isomorphism, then the restriction `U' ⟶ U` is
étale, being an isomorphism. -/
theorem isEtale_openComplementRestriction (f : X' ⟶ X) (T : Set (points B S hS X))
    (h : IsIso (pullback.snd f (openSubspaceOfPoints B S hS X Tᶜ).ι)) :
    IsEtale B S hS (openComplementRestriction B S hS f T) :=
  have := isIso_openComplementRestriction B S hS f T h
  isEtale_of_isIso B S hS _

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### The reduction to the affine case -/

/-- The reduction of **Stacks 0GDH** to the affine case, which this library does not carry.

Granted that `X` is locally Noetherian, `f` is locally of finite type and `U' → U` is smooth,
it produces for every affine representable étale square over `f_{/T}` presented by an arrow
`g : A → C` of `WAdm^{Noeth}` the affine data of the source's proof: a Noetherian ring `A₀`,
an ideal `I₀ ⊆ A₀` and a finite type `A₀`-algebra `C₀` with `Spec C₀ → Spec A₀` smooth over
`Spec A₀ ∖ V(I₀)`, together with the comparison turning rig-smoothness of the `I₀`-adic
completion `C₀^` over `(A₀, I₀)` into rig-smoothness of `g` over an ideal of definition of
`A`.

The source assembles it from Properties of Spaces, Lemma 03FX, the cartesian completion
squares of Stacks 0APV, the identification `X_{/T} = Spf(A^∧)` in the proof of Stacks 0AQ1,
and the fact that local finite type, smoothness and local Noetherianity are étale local on
source and target. -/
abbrev ChartSquareReducesToSmoothAwayFrom (f : X' ⟶ X) (T : Set (Space.points B S hS X)) :
    Prop :=
  Space.IsLocallyNoetherian B S hS X →
    Space.IsLocallyOfFiniteType B S hS f →
      Space.IsSmooth B S hS (Space.openComplementRestriction B S hS f T) →
        ∀ (U V : FppfSheaf B S hS)
          (a : U ⟶ Space.completionSheaf B S hS X' (Space.pointsMap B S hS X' f ⁻¹' T))
          (b : V ⟶ Space.completionSheaf B S hS X T) (t : U ⟶ V),
          IsAffineFormalAlgebraicSpace B S hS U → IsAffineFormalAlgebraicSpace B S hS V →
          IsRepresentableEtale B S hS a → IsRepresentableEtale B S hS b →
          a ≫ Space.completionSheafMap B S hS f T = t ≫ b →
          ∀ (A C : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
            [IsLinearTopology A A] [IsNoetherianRing A] [CommRing C] [TopologicalSpace C]
            [IsTopologicalRing C] [IsLinearTopology C C] [IsNoetherianRing C],
            TopologicalRing.IsAdic A → TopologicalRing.IsAdic C →
            ∀ (hA : TopologicalRing.IsWeaklyAdmissible A) (D : QuotientSystem B S hS A)
              (E : QuotientSystem B S hS C) (eU : U ≅ formalSpectrum E)
              (eV : V ≅ formalSpectrum D) (g : ContinuousHom D E),
              t = eU.hom ≫ formalSpectrumMap hA g ≫ eV.inv →
                ∃ (A₀ : Type u) (_ : CommRing A₀) (_ : IsNoetherianRing A₀) (I₀ : Ideal A₀)
                  (C₀ : Type u) (_ : CommRing C₀) (_ : Algebra A₀ C₀)
                  (_ : Algebra.FiniteType A₀ C₀),
                  Rig.SmoothAwayFrom A₀ I₀ C₀ ∧
                    (Rig.IsRigSmooth (Rig.adicCompletionObj I₀ (B := C₀)) →
                      ∃ (hft : Rig.FiniteTypeAdicAlgebraForEveryIdeal g.toRingHom)
                        (I : Ideal A) (hI : TopologicalRing.IsIdealOfDefinition I),
                        Rig.IsRigSmooth (Rig.adicFiniteTypeAlgebra g.toRingHom hft I hI))

/-- The reduction of **Stacks 0AR2** to the affine case, which this library does not carry.

It is `AlgebraicGeometry.FormalSpace.ChartSquareReducesToSmoothAwayFrom` with smoothness of
`U' → U` replaced by étaleness, smoothness of `Spec C₀ → Spec A₀` over `Spec A₀ ∖ V(I₀)`
replaced by étaleness there, and the comparison landing in rig-étaleness of `g` in the sense
of Definition 0GCV: this is the substitution the source's proof of Stacks 0AR2 describes,
Lemmas 0GAK and 0GCQ being replaced by Lemmas 0ALQ and 0GCZ. -/
abbrev ChartSquareReducesToIsEtaleOutside (f : X' ⟶ X) (T : Set (Space.points B S hS X)) :
    Prop :=
  Space.IsLocallyNoetherian B S hS X →
    Space.IsLocallyOfFiniteType B S hS f →
      Space.IsEtale B S hS (Space.openComplementRestriction B S hS f T) →
        ∀ (U V : FppfSheaf B S hS)
          (a : U ⟶ Space.completionSheaf B S hS X' (Space.pointsMap B S hS X' f ⁻¹' T))
          (b : V ⟶ Space.completionSheaf B S hS X T) (t : U ⟶ V),
          IsAffineFormalAlgebraicSpace B S hS U → IsAffineFormalAlgebraicSpace B S hS V →
          IsRepresentableEtale B S hS a → IsRepresentableEtale B S hS b →
          a ≫ Space.completionSheafMap B S hS f T = t ≫ b →
          ∀ (A C : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
            [IsLinearTopology A A] [IsNoetherianRing A] [CommRing C] [TopologicalSpace C]
            [IsTopologicalRing C] [IsLinearTopology C C] [IsNoetherianRing C],
            TopologicalRing.IsAdic A → TopologicalRing.IsAdic C →
            ∀ (hA : TopologicalRing.IsWeaklyAdmissible A) (D : QuotientSystem B S hS A)
              (E : QuotientSystem B S hS C) (eU : U ≅ formalSpectrum E)
              (eV : V ≅ formalSpectrum D) (g : ContinuousHom D E),
              t = eU.hom ≫ formalSpectrumMap hA g ≫ eV.inv →
                ∃ (A₀ : Type u) (_ : CommRing A₀) (_ : IsNoetherianRing A₀) (I₀ : Ideal A₀)
                  (C₀ : Type u) (_ : CommRing C₀) (_ : Algebra A₀ C₀)
                  (_ : Algebra.FiniteType A₀ C₀),
                  Rig.IsEtaleOutside I₀ C₀ ∧
                    (Rig.IsRigEtale (Rig.adicCompletionObj I₀ (B := C₀)) →
                      RingHom.IsRigEtale g.toRingHom)

/-! ### Stacks 0GDH and Stacks 0AR2 -/

variable {B S hS}

/-- **Stacks 0GDH.** In the situation of Stacks 0GDB, if `X` is locally Noetherian, `f` is
locally of finite type and `U' → U` is smooth, then `f_{/T}` is rig-smooth.

Granted the reduction to the affine case, the lemma is part (1) of Stacks 0GAK applied to the
affine data that reduction produces, exactly as in the source. -/
@[stacks 0GDH "the affine case, which is part (1) of Stacks 0GAK \
(`Rig.isRigSmooth_adicCompletionObj_of_smoothAwayFrom`), applied through the reduction to the \
affine case carried as the hypothesis `hred`: granted the three hypotheses of the lemma it \
produces, for each affine representable étale square over `f_{/T}`, the Noetherian ring `A₀`, \
the ideal `I₀` and the finite type `A₀`-algebra `C₀` smooth over `Spec A₀` minus `V(I₀)` of \
the source's proof, together with the comparison of rig-smoothness of `C₀` completed with \
rig-smoothness of the arrow of `WAdm^{Noeth}` presenting the square. The source assembles \
that reduction from Properties of Spaces, Lemma 03FX, the cartesian completion squares of \
Stacks 0APV, the identification of a chart of the completion with a formal spectrum in the \
proof of Stacks 0AQ1, and the étale locality of local finite type, of smoothness and of local \
Noetherianity, none of which this library carries in that combination"]
theorem isRigSmooth_completionSheafMap {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X' ⟶ X)
    (T : Set (Space.points B S hS X))
    (hX : Space.IsLocallyNoetherian B S hS X)
    (hf : Space.IsLocallyOfFiniteType B S hS f)
    (hsm : Space.IsSmooth B S hS (Space.openComplementRestriction B S hS f T))
    (hred : ChartSquareReducesToSmoothAwayFrom B S hS f T) :
    IsRigSmooth B S hS (Space.completionSheafMap B S hS f T) := by
  intro U V hU hV a b t ha hb hae hbe hcomm A C _ _ _ _ _ _ _ _ _ _ hAadic hCadic hA D E
    eU eV g hg
  obtain ⟨A₀, _, _, I₀, C₀, _, _, _, hsmooth, hcomp⟩ :=
    hred hX hf hsm U V a b t hU hV ⟨ha, hae⟩ ⟨hb, hbe⟩ hcomm A C hAadic hCadic hA D E eU eV g hg
  exact hcomp (Rig.isRigSmooth_adicCompletionObj_of_smoothAwayFrom I₀ hsmooth)

/-- **Stacks 0AR2.** In the situation of Stacks 0GDB, if `X` is locally Noetherian, `f` is
locally of finite type and `U' → U` is étale, then `f_{/T}` is rig-étale.

Granted the reduction to the affine case, the lemma is part (1) of Stacks 0ALQ applied to the
affine data that reduction produces; this is the proof of Stacks 0GDH with Lemmas 0GAK and
0GCQ replaced by Lemmas 0ALQ and 0GCZ, as the source says. -/
@[stacks 0AR2 "the affine case, which is part (1) of Stacks 0ALQ \
(`Rig.isRigEtale_adicCompletionObj_of_isEtaleOutside`), applied through the reduction to the \
affine case carried as the hypothesis `hred`: granted the three hypotheses of the lemma it \
produces, for each affine representable étale square over `f_{/T}`, the Noetherian ring `A₀`, \
the ideal `I₀` and the finite type `A₀`-algebra `C₀` étale over `Spec A₀` minus `V(I₀)` of \
the source's proof, together with the comparison of rig-étaleness of `C₀` completed with \
rig-étaleness of the arrow of `WAdm^{Noeth}` presenting the square. This is the substitution \
of Lemmas 0ALQ and 0GCZ for Lemmas 0GAK and 0GCQ that the source's proof prescribes; the \
reduction itself is assembled in the source from Properties of Spaces, Lemma 03FX, the \
cartesian completion squares of Stacks 0APV, the identification of a chart of the completion \
with a formal spectrum in the proof of Stacks 0AQ1, and the étale locality of local finite \
type, of étaleness and of local Noetherianity, none of which this library carries in that \
combination"]
theorem isRigEtale_completionSheafMap {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X' ⟶ X)
    (T : Set (Space.points B S hS X))
    (hX : Space.IsLocallyNoetherian B S hS X)
    (hf : Space.IsLocallyOfFiniteType B S hS f)
    (het : Space.IsEtale B S hS (Space.openComplementRestriction B S hS f T))
    (hred : ChartSquareReducesToIsEtaleOutside B S hS f T) :
    IsRigEtale B S hS (Space.completionSheafMap B S hS f T) := by
  intro U V hU hV a b t ha hb hae hbe hcomm A C _ _ _ _ _ _ _ _ _ _ hAadic hCadic hA D E
    eU eV g hg
  obtain ⟨A₀, _, _, I₀, C₀, _, _, _, hetale, hcomp⟩ :=
    hred hX hf het U V a b t hU hV ⟨ha, hae⟩ ⟨hb, hbe⟩ hcomm A C hAadic hCadic hA D E eU eV g hg
  exact hcomp (Rig.isRigEtale_adicCompletionObj_of_isEtaleOutside I₀ hetale)

/-- **Stacks 0GD0** applied to **Stacks 0AR2**: in the situation of Stacks 0GDB, if `X` is
locally Noetherian, `f` is locally of finite type and `U' → U` is étale, then `f_{/T}` is
rig-smooth. -/
theorem isRigSmooth_completionSheafMap_of_isEtale
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X' ⟶ X)
    (T : Set (Space.points B S hS X))
    (hX : Space.IsLocallyNoetherian B S hS X)
    (hf : Space.IsLocallyOfFiniteType B S hS f)
    (het : Space.IsEtale B S hS (Space.openComplementRestriction B S hS f T))
    (hred : ChartSquareReducesToIsEtaleOutside B S hS f T) :
    IsRigSmooth B S hS (Space.completionSheafMap B S hS f T) :=
  isRigSmooth_of_isRigEtale B S hS _
    (isRigEtale_completionSheafMap f T hX hf het hred)

/-! ### Stacks 0AR5, the completion arrow -/

section Completion

attribute [local instance] Space.pointTopology

variable (B S hS)

/-- The right-hand collection of the equation **Stacks 0AR5**: morphisms `g : W ⟶ X_{/T}` of
formal algebraic spaces over `S` with `W` locally Noetherian and `g` rig-étale, as a full
subcategory of the category of formal sheaves over `X_{/T}`. -/
abbrev RigEtaleOverCompletion (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (T : Set (Space.points B S hS X)) :=
  ObjectProperty.FullSubcategory
    (fun W : Over (Space.completionSheaf B S hS X T) =>
      IsFormalAlgebraicSpace B S hS W.left ∧ IsLocallyNoetherian B S hS W.left ∧
        IsRigEtale B S hS W.hom)

/-- **Stacks 0AIZ**, which this library does not carry: the completion of an algebraic space
over `S` along a closed set of points is a formal algebraic space. Stated for the algebraic
spaces over `X` appearing in the left-hand collection of Stacks 0AR5, whose own closed set is
the inverse image of `T`. The library defines the completion for an arbitrary presheaf and an
arbitrary set of points and proves only the affine case of Stacks 0AIZ, which is Stacks 0AIY,
as `AlgebraicGeometry.FormalSpace.hasSomeSurjectivePresentation_completionSheaf`. -/
abbrev IsFormalAlgebraicSpaceCompletionSheaf (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (T : Set (Space.points B S hS X)) : Prop :=
  IsClosed T → ∀ {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (h : Z ⟶ X),
    IsAlgebraicSpace B S hS Z →
      IsFormalAlgebraicSpace B S hS
        (Space.completionSheaf B S hS Z (Space.pointsMap B S hS Z h ⁻¹' T))

/-- The local Noetherianity half of the right-hand collection of Stacks 0AR5, which this
library does not carry: the completion of an algebraic space locally of finite type over a
locally Noetherian algebraic space along the inverse image of a closed set is locally
Noetherian in the sense of **Stacks 0AKY**. It packages Properties of Spaces, Lemma 01T6, that
an algebraic space locally of finite type over a locally Noetherian one is locally Noetherian,
with the identification of a chart of the completion with the formal spectrum of a Noetherian
adic ring from the proof of **Stacks 0AQ1**. -/
abbrev IsLocallyNoetherianCompletionSheaf (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (T : Set (Space.points B S hS X)) : Prop :=
  IsClosed T → Space.IsLocallyNoetherian B S hS X →
    ∀ {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (h : Z ⟶ X), IsAlgebraicSpace B S hS Z →
      Space.IsLocallyOfFiniteType B S hS h →
        IsLocallyNoetherian B S hS
          (Space.completionSheaf B S hS Z (Space.pointsMap B S hS Z h ⁻¹' T))

variable {B S hS}

/-- **Stacks 0AR5.** The arrow of the displayed equation: a morphism `f : X' ⟶ X` of algebraic
spaces over `S` which is locally of finite type and an isomorphism over `U` is sent to
`f_{/T} : X'_{/T'} ⟶ X_{/T}`, a rig-étale morphism with locally Noetherian source.

That `f_{/T}` is rig-étale is Stacks 0AR2 applied to `U' ⟶ U`, which is an isomorphism — and
hence étale — because `U'` is the fibre product of `U` with `f`. -/
@[stacks 0AR5 "the arrow of the displayed equation, that is the assignment sending a morphism \
locally of finite type which is an isomorphism over `U` to its completion along `T`, together \
with the three conditions placing the result in the right-hand collection. The rig-étaleness, \
which is what the source says makes the arrow well defined, is Stacks 0AR2 \
(`AlgebraicGeometry.FormalSpace.isRigEtale_completionSheafMap`) applied through the proof \
here that `U'` is the fibre product of `U` with `f`, so that the modification condition makes \
`U' ⟶ U` an isomorphism and therefore étale. The two conditions on the source `X'_{/T'}` are \
hypotheses: Stacks 0AIZ, that a completion along a closed set is a formal algebraic space, as \
`h0AIZ`, and its locally Noetherian refinement as `hnoeth`; neither is carried by this \
library, which proves only the affine case Stacks 0AIY of the first. The reduction of Stacks \
0AR2 to the affine case is forwarded as `hred`"]
def completionOfFiniteTypeModification {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (T : Set (Space.points B S hS X)) (hT : IsClosed T)
    (hX : Space.IsLocallyNoetherian B S hS X)
    (M : Space.FiniteTypeModification B S hS (Space.openSubspaceOfPoints B S hS X Tᶜ))
    (h0AIZ : IsFormalAlgebraicSpaceCompletionSheaf B S hS X T)
    (hnoeth : IsLocallyNoetherianCompletionSheaf B S hS X T)
    (hred : ChartSquareReducesToIsEtaleOutside B S hS M.obj.hom T) :
    RigEtaleOverCompletion B S hS X T :=
  ⟨Over.mk (Space.completionSheafMap B S hS M.obj.hom T),
    h0AIZ hT M.obj.hom M.property.1.1,
    hnoeth hT hX M.obj.hom M.property.1.1 M.property.2,
    isRigEtale_completionSheafMap M.obj.hom T hX M.property.2
      (Space.isEtale_openComplementRestriction B S hS M.obj.hom T M.property.1.2) hred⟩

/-- The arrow of Stacks 0AR5 sends `f : X' ⟶ X` to `f_{/T} : X'_{/T'} ⟶ X_{/T}`. -/
theorem completionOfFiniteTypeModification_obj {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (T : Set (Space.points B S hS X)) (hT : IsClosed T)
    (hX : Space.IsLocallyNoetherian B S hS X)
    (M : Space.FiniteTypeModification B S hS (Space.openSubspaceOfPoints B S hS X Tᶜ))
    (h0AIZ : IsFormalAlgebraicSpaceCompletionSheaf B S hS X T)
    (hnoeth : IsLocallyNoetherianCompletionSheaf B S hS X T)
    (hred : ChartSquareReducesToIsEtaleOutside B S hS M.obj.hom T) :
    (completionOfFiniteTypeModification T hT hX M h0AIZ hnoeth hred).obj =
      Over.mk (Space.completionSheafMap B S hS M.obj.hom T) :=
  rfl

end Completion

end AlgebraicGeometry.FormalSpace

end
