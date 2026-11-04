module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.BasicOpenLocal
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PseudoCoherentLocal
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PushforwardVanishing
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictTarget
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.SchemeReflect

/-!
# Gluing relative pseudo-coherence along a standard affine open cover, Stacks 09VE

Let `f : X ⟶ S` be a morphism of affine schemes locally of finite type, let `E` be an object of
`D(𝒪_X)` and let `X = ⋃ X_{gⱼ}` be a standard affine open cover. Stacks 09VE says that the
equivalent conditions of Stacks 09VC hold for the pair `(X ⟶ S, E)` if and only if they hold for
each pair `(X_{gⱼ} ⟶ S, E|_{X_{gⱼ}})`.

The implication from the cover to `X` is proved here, granted the side condition of Stacks 09VA at
the intermediate schemes that occur; the converse implication is the second paragraph of Stacks
09VD, `AlgebraicGeometry.Scheme.Modules.exists_isPseudoCoherentFromAfterPushforward_basicOpen`.

## Main results

* `AlgebraicGeometry.RingedSpace.IsPseudoCoherentFrom.of_isZero`: a zero object of the derived
  category of `𝒪`-modules on a ringed space is `m`-pseudo-coherent for every `m`.

In namespace `AlgebraicGeometry.Scheme.Modules`:

* `isPseudoCoherentFrom_derivedRestrictModules_of_morphismRestrict`: the converse of
  `IsPseudoCoherentFromAfterPushforward.morphismRestrict` — the local condition of Stacks 09UI at
  the restricted closed immersion `i|_W : i⁻¹W ⟶ W` implies `m`-pseudo-coherence of `(Ri_*E)|_W`.
* `isPseudoCoherentFromAfterPushforward_morphismRestrict_basicOpen`: the local step of the proof
  below — the equivalent conditions of Stacks 09VC for `(i⁻¹D(y) ⟶ S, E|_{i⁻¹D(y)})` imply the
  local condition of Stacks 09UI at the closed immersion `i|_{D(y)} : i⁻¹D(y) ⟶ D(y)` into the
  standard open `D(y)` of an affine space over `S`.
* `exists_isPseudoCoherentFromAfterPushforward_of_forall_basicOpen`: **the implication (1) ⇒ (2)
  of Stacks 09VE.**
* `isPseudoCoherentFrom_some_iff_forall_basicOpen`: **Stacks 09VE**, granted the side condition of
  Stacks 09VA.

## Implementation notes

**The intermediate scheme `T` of the source's proof is not needed, and neither is the partition of
unity.** The source writes `1 = ∑ fᵢgᵢ` in `Γ(X, ⊤)`, forms the surjections
`R[xᵢ, yᵢ, zᵢ] ↠ R[xᵢ, yᵢ, zᵢ]/(∑ yᵢzᵢ - 1) ↠ Γ(X, ⊤)` and pushes `E` forward to
`T = Spec R[xᵢ, yᵢ, zᵢ]/(∑ yᵢzᵢ - 1)`, which it then covers by the opens `D(y_{i₀})`. None of that
is used below. Take *any* closed immersion `i : X ⟶ 𝔸ᴹ_S` factoring `f`
(`AlgebraicGeometry.exists_isClosedImmersion_affineSpace`). Since `i` is a closed immersion of
affine schemes, `i` is surjective on global sections, so each `gⱼ` lifts to a `yⱼ` on `𝔸ᴹ_S` with
`i⁻¹D(yⱼ) = X_{gⱼ}`. The opens `D(yⱼ)` therefore cover the image of `i`, and together with the open
complement of that image they cover `𝔸ᴹ_S`. Pseudo-coherence is local
(`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_local_restrict`), so it is enough to treat
each piece: on the complement of the image `Ri_*E` vanishes
(`AlgebraicGeometry.RingedSpace.isZero_derivedRestrict_derivedPushforward_of_preimage_eq_bot`), and
on `D(yⱼ)` it is the derived pushforward of `E|_{X_{gⱼ}}` along `i|_{D(yⱼ)}`.

**A defect in the source.** The proof of Stacks 09VE asserts that
`R[xᵢ, yᵢ, zᵢ, 1/y_{i₀}]/(∑ yᵢzᵢ - 1)` "is isomorphic to a polynomial ring over `R`". It is not:
taking one index and no `xᵢ` it is `R[y, y⁻¹]`, a Laurent extension, whose unit group is strictly
larger than that of `R` for `R` a field, while the units of a polynomial ring over a field are the
nonzero constants. What the source needs at that point is only that the equivalent conditions of
Stacks 09VC may be read off at a closed immersion into *that* scheme rather than into an affine
space, which is Stacks 09VC together with the side condition of Stacks 09VA; the argument below
takes that route and so does not depend on the false assertion. In the formulation here the scheme
in question is a standard open `D(y)` of an affine space over `S`, and all that is used about it is
that it is affine and locally of finite type over `S`.

**Why there are two side-condition hypotheses.** Stacks 09VE is stated without hypotheses, but its
proof applies Stacks 09VA twice, at two different kinds of closed immersion, and the side condition
of Stacks 09VA — that the pushforward of the structure sheaf be a pseudo-coherent module — is a
genuine condition on the source. Here those two kinds are: closed immersions `𝔸ᵃ_S ⟶ 𝔸ᵇ_S` of
affine spaces over `S`, which is the hypothesis of
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFrom_some_iff_forall_of_fin`; and closed
immersions `D(y) ⟶ 𝔸ᴺ_S` of a standard open of an affine space over `S`, which is the hypothesis of
`AlgebraicGeometry.Scheme.Modules.exists_isPseudoCoherentFromAfterPushforward_basicOpen`. Both are
asked for in exactly the shapes those results use, so that discharging them discharges the
hypotheses here with no restatement. No `stacks` attribute is placed for that reason: Stacks 09VE
itself carries neither hypothesis.

**The two vocabularies of restriction.** `AlgebraicGeometry.Scheme.Modules.restrictFunctor U.ι` and
`AlgebraicGeometry.RingedSpace.restrictModules` are *not* definitionally interchangeable — they are
two spellings of restriction to an open subscheme in two spellings of the category of
`𝒪`-modules — and the identification between them is not installed by typeclass synthesis. It is
not assumed here:
`AlgebraicGeometry.RingedSpace.derivedRestrictModulesIsoRestrictFunctor`, which is constructed at
the level of isomorphisms of functors rather than componentwise, is what crosses between them, and
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFrom_derivedRestrictModules_of_morphismRestrict`
below is the only place the crossing is used.

**An expected linter finding.**
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFrom_some_iff_forall_basicOpen` carries the
instance `[QuasiCompact f]` that Stacks 09VE's statement of the hypotheses includes and
that the proof does not use — it is automatic for a morphism of affine schemes. It is kept because
the statement is the contract, so `lake lint` reports one `unusedArguments` finding on this file;
the same pattern is already present at
`AlgebraicGeometry.Scheme.Hom.IsPseudoCoherentFrom`
(`StacksFrontier/AlgebraicGeometry/PseudoCoherent/Relative.lean`) and
`AlgebraicGeometry.AffineSpace.exists_isClosedImmersion_sum`
(`StacksFrontier/AlgebraicGeometry/PseudoCoherent/ClosedImmersion.lean`).

The derived categories are the ones provided by `CategoryTheory.HasDerivedCategory.standard`, which
is made a local instance; there is no global instance, so a user of these results makes the same
declaration.

## References

* [The Stacks Project, Lemma 36.61.5 (09VE)](https://stacks.math.columbia.edu/tag/09VE)
* [The Stacks Project, Lemma 36.61.4 (09VD)](https://stacks.math.columbia.edu/tag/09VD)
* [The Stacks Project, Lemma 36.61.2 (09VC)](https://stacks.math.columbia.edu/tag/09VC)
* [The Stacks Project, Lemma 36.60.9 (09VA)](https://stacks.math.columbia.edu/tag/09VA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect
open scoped AlgebraicGeometry ZeroObject

universe d u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

/-! ### A zero object is pseudo-coherent -/

/-- Every term of the zero complex of `𝒪_X`-modules is a zero object. -/
private theorem isZero_X_zero {X : RingedSpace.{u, u}} {j : ℤ} :
    IsZero ((0 : CochainComplex (OXMod.{u, u} X) ℤ).X j) :=
  (HomologicalComplex.eval _ (ComplexShape.up ℤ) j).map_isZero (isZero_zero _)

/-- A complex of `𝒪_X`-modules all of whose terms are zero is `m`-pseudo-coherent for every `m`:
the zero complex is a strictly perfect approximation of it on all of `X`, since every cohomology
object in sight vanishes. -/
public theorem isPseudoCoherentComplexFrom_of_forall_isZero {X : RingedSpace.{u, u}}
    {K : CochainComplex (OXMod.{u, u} X) ℤ} (hK : ∀ j, IsZero (K.X j)) (m : ℤ) :
    IsPseudoCoherentComplexFrom K m := by
  intro x
  have hres : IsZero (restrictComplex K (⊤ : Opens X.carrier)) := by
    rw [IsZero.iff_id_eq_zero]
    refine HomologicalComplex.hom_ext _ _ fun j => ?_
    exact ((restrictModules X ⊤).isZero_obj (hK j)).eq_of_src _ _
  refine ⟨⊤, Opens.mem_top x, 0, isStrictlyPerfect_of_forall_isZero fun _ => isZero_X_zero, 0,
    fun j _ => ?_, ?_⟩
  · exact ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) j).isZero_obj
      (isZero_zero _)).isIso
      ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) j).isZero_obj hres) _
  · exact ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) m).isZero_obj hres).epi _

/-- **A zero object of `D(𝒪_X)` is `m`-pseudo-coherent, for every `m`.** It is represented by the
zero complex, which is `m`-pseudo-coherent by
`AlgebraicGeometry.RingedSpace.isPseudoCoherentComplexFrom_of_forall_isZero`.

This is what makes the open complement of the closed image of a closed immersion harmless in a
local argument about a derived pushforward; compare
`AlgebraicGeometry.RingedSpace.exists_strictlyPerfect_approximation_of_isZero`, which supplies the
same content in the shape of an approximation rather than of the predicate. -/
public theorem IsPseudoCoherentFrom.of_isZero {X : RingedSpace.{u, u}}
    [HasDerivedCategory.{d} (OXMod.{u, u} X)] {E : DerivedCategory (OXMod.{u, u} X)}
    (hE : IsZero E) (m : ℤ) : IsPseudoCoherentFrom E m :=
  ⟨0, isPseudoCoherentComplexFrom_of_forall_isZero (X := X)
      (fun _ => isZero_X_zero) m,
    ⟨(DerivedCategory.Q.isZero_obj (isZero_zero _)).iso hE⟩⟩

end AlgebraicGeometry.RingedSpace

namespace AlgebraicGeometry.Scheme.Modules

/-! ### Restricting the target of a closed immersion, read backwards -/

/-- **The converse of
`AlgebraicGeometry.Scheme.Modules.IsPseudoCoherentFromAfterPushforward.morphismRestrict`.** Let
`i : Z ⟶ Y` be a closed immersion of schemes and let `W` be an open subscheme of `Y`. If the
derived pushforward of `E|_{i⁻¹W}` along the restricted closed immersion `i|_W : i⁻¹W ⟶ W` is
`m`-pseudo-coherent on `W`, then the restriction `(Ri_*E)|_W` is `m`-pseudo-coherent.

This is the proof of
`AlgebraicGeometry.Scheme.Modules.IsPseudoCoherentFromAfterPushforward.morphismRestrict` read in
the opposite direction: each of its steps is an isomorphism or an iff, namely the crossing
`AlgebraicGeometry.RingedSpace.derivedRestrictModulesIsoRestrictFunctor` between the two
vocabularies of restriction, the transport
`AlgebraicGeometry.RingedSpace.IsPseudoCoherentFrom.derivedPushforwardOXMod_congr` along the
identity of the two restricted morphisms, and the derived base-change square
`AlgebraicGeometry.RingedSpace.derivedRestrictPushforwardObjIso`. No pseudo-coherence theory is
involved, and neither half of Stacks 09VA is. -/
public theorem isPseudoCoherentFrom_derivedRestrictModules_of_morphismRestrict {Z Y : Scheme.{u}}
    (i : Z ⟶ Y) [IsClosedImmersion i] (W : Y.Opens) (E : DerivedCategory Z.Modules) (m : ℤ)
    (h : IsPseudoCoherentFromAfterPushforward (i ∣_ W)
      ((restrictFunctor (i ⁻¹ᵁ W).ι).mapDerivedCategory.obj E) m) :
    RingedSpace.IsPseudoCoherentFrom
        (X := Y.toRingedSpace.restrict W.isOpenEmbedding)
        ((RingedSpace.derivedRestrictModules Y.toRingedSpace W).obj
          ((RingedSpace.derivedPushforwardOXMod i.toLRSHom.toShHom
            (Stacks.ClosedImmersion.isClosedEmbedding_base_toShHom i)).obj E)) m := by
  have hi : Topology.IsClosedEmbedding i.toLRSHom.toShHom.hom.base :=
    Stacks.ClosedImmersion.isClosedEmbedding_base_toShHom i
  have hiW : Topology.IsClosedEmbedding (i ∣_ W).toLRSHom.toShHom.hom.base :=
    Stacks.ClosedImmersion.isClosedEmbedding_base_toShHom (i ∣_ W)
  have k₁ : RingedSpace.IsPseudoCoherentFrom (X := W.toScheme.toRingedSpace)
      ((RingedSpace.derivedPushforwardOXMod (i ∣_ W).toLRSHom.toShHom hiW).obj
        ((restrictFunctor (i ⁻¹ᵁ W).ι).mapDerivedCategory.obj E)) m :=
    (isPseudoCoherentFromAfterPushforward_iff (i ∣_ W) _ m).mp h
  have k₂ := k₁.of_iso
    ((RingedSpace.derivedPushforwardOXMod (i ∣_ W).toLRSHom.toShHom hiW).mapIso
      ((RingedSpace.derivedRestrictModulesIsoRestrictFunctor Z (i ⁻¹ᵁ W)).app E).symm)
  have k₃ := RingedSpace.IsPseudoCoherentFrom.derivedPushforwardOXMod_congr _ _
    (RingedSpace.restrictHom_eq_morphismRestrict' i W).symm hiW
    (RingedSpace.isClosedEmbedding_restrictHom i.toLRSHom.toShHom W hi) _ _ k₂
  exact k₃.of_iso
    (RingedSpace.derivedRestrictPushforwardObjIso i.toLRSHom.toShHom W hi E).symm

/-! ### The local step of Stacks 09VE -/

/-- **The local step of the proof of Stacks 09VE.** Let `i : X ⟶ 𝔸ᴹ_S` be a closed immersion of
affine schemes factoring `f : X ⟶ S`, and let `y` be a global section of `𝔸ᴹ_S`. Granted the side
condition of Stacks 09VA at closed immersions of affine spaces over `S` and at closed immersions of
`D(y)` into affine spaces over `S`, the equivalent conditions of Stacks 09VC for the pair
`(i⁻¹D(y) ⟶ S, E|_{i⁻¹D(y)})` imply the local condition of Stacks 09UI at the restricted closed
immersion `i|_{D(y)} : i⁻¹D(y) ⟶ D(y)`.

The standard open `D(y)` is affine and `D(y) ⟶ S` is locally of finite type, being an open
immersion followed by the structure morphism of an affine space, so there is a closed immersion
`q : D(y) ⟶ 𝔸ᴺ_S` factoring it. By Stacks 09VC (in the form
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFrom_some_iff_forall_of_fin`) the hypothesis
holds at the closed immersion `i|_{D(y)} ≫ q`, and the converse half of Stacks 09VA
(`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFrom_of_pushforward_mapDerivedCategory`) strips
the factor `q`.

This is the step at which the source invokes its false claim that `D(y) ∩ T` is an affine space
over `S`; nothing of the kind is needed, only that `D(y)` is affine and of finite type over `S`. -/
public theorem isPseudoCoherentFromAfterPushforward_morphismRestrict_basicOpen {X S : Scheme.{u}}
    [IsAffine X] [IsAffine S] {M : ℕ} (i : X ⟶ AffineSpace (ULift.{u} (Fin M)) S)
    [IsClosedImmersion i] (f : X ⟶ S) [LocallyOfFiniteType f]
    (hover : i ≫ (AffineSpace.over (ULift.{u} (Fin M)) S).hom = f)
    (y : Γ(AffineSpace (ULift.{u} (Fin M)) S, ⊤))
    (hO : ∀ {a b : ℕ}
      (p : AffineSpace (ULift.{u} (Fin a)) S ⟶ AffineSpace (ULift.{u} (Fin b)) S)
      [IsClosedImmersion p],
      RingedSpace.IsPseudoCoherent (X := (AffineSpace (ULift.{u} (Fin b)) S).toRingedSpace)
        ((DerivedCategory.singleFunctor (AffineSpace (ULift.{u} (Fin b)) S).Modules 0).obj
          ((pushforward p).obj
            (SheafOfModules.unit (AffineSpace (ULift.{u} (Fin a)) S).ringCatSheaf))))
    (hOy : PushforwardStructureSheafPseudoCoherent S
      ((AffineSpace (ULift.{u} (Fin M)) S).basicOpen y).toScheme)
    (E : DerivedCategory X.Modules) (m : ℤ)
    (h : ∃ (k : ℕ) (l : (i ⁻¹ᵁ (AffineSpace (ULift.{u} (Fin M)) S).basicOpen y).toScheme ⟶
        AffineSpace (ULift.{u} (Fin k)) S),
      IsClosedImmersion l ∧
        l ≫ (AffineSpace.over (ULift.{u} (Fin k)) S).hom =
          (i ⁻¹ᵁ (AffineSpace (ULift.{u} (Fin M)) S).basicOpen y).ι ≫ f ∧
          IsPseudoCoherentFromAfterPushforward l
            ((restrictFunctor
              (i ⁻¹ᵁ (AffineSpace (ULift.{u} (Fin M)) S).basicOpen y).ι).mapDerivedCategory.obj E)
            m) :
    IsPseudoCoherentFromAfterPushforward (i ∣_ (AffineSpace (ULift.{u} (Fin M)) S).basicOpen y)
      ((restrictFunctor
        (i ⁻¹ᵁ (AffineSpace (ULift.{u} (Fin M)) S).basicOpen y).ι).mapDerivedCategory.obj E) m := by
  have hWa : IsAffineOpen ((AffineSpace (ULift.{u} (Fin M)) S).basicOpen y) :=
    (isAffineOpen_top _).basicOpen y
  have hWaff : IsAffine ((AffineSpace (ULift.{u} (Fin M)) S).basicOpen y).toScheme := hWa
  have hUaff : IsAffine (i ⁻¹ᵁ (AffineSpace (ULift.{u} (Fin M)) S).basicOpen y).toScheme := by
    rw [Scheme.preimage_basicOpen_top]
    exact (isAffineOpen_top X).basicOpen _
  have hoverft : LocallyOfFiniteType ((AffineSpace.over (ULift.{u} (Fin M)) S).hom) := by
    rw [AffineSpace.over_hom_eq]
    infer_instance
  have hWft : LocallyOfFiniteType
      (((AffineSpace (ULift.{u} (Fin M)) S).basicOpen y).ι ≫
        (AffineSpace.over (ULift.{u} (Fin M)) S).hom) :=
    MorphismProperty.comp_mem _ _ _ inferInstance hoverft
  obtain ⟨N, q, hq, hqo⟩ := exists_isClosedImmersion_affineSpace
    (((AffineSpace (ULift.{u} (Fin M)) S).basicOpen y).ι ≫
      (AffineSpace.over (ULift.{u} (Fin M)) S).hom)
  have := hq
  have key : IsPseudoCoherentFromAfterPushforward
      ((i ∣_ (AffineSpace (ULift.{u} (Fin M)) S).basicOpen y) ≫ q) _ m :=
    (isPseudoCoherentFrom_some_iff_forall_of_fin
      ((i ⁻¹ᵁ (AffineSpace (ULift.{u} (Fin M)) S).basicOpen y).ι ≫ f) _ m hO).mp h N _
      inferInstance (by rw [Category.assoc, hqo, ← Category.assoc, morphismRestrict_ι,
        Category.assoc, hover])
  rw [isPseudoCoherentFromAfterPushforward_comp_iff] at key
  rw [isPseudoCoherentFromAfterPushforward_iff]
  exact isPseudoCoherentFrom_of_pushforward_mapDerivedCategory q (hOy N q hq) m _ key

/-! ### Stacks 09VE -/

/-- **The implication (1) ⇒ (2) of Stacks 09VE.** Let `f : X ⟶ S` be a morphism of affine schemes
locally of finite type, let `E` be an object of `D(𝒪_X)` and let the basic opens of
`g : Fin n → Γ(X, ⊤)` be a standard affine open cover of `X`. Granted the side condition of
Stacks 09VA at the two kinds of closed immersion that occur, if the equivalent conditions of
Stacks 09VC hold for each pair `(X_{gⱼ} ⟶ S, E|_{X_{gⱼ}})` then they hold for `(X ⟶ S, E)`.

Take any closed immersion `i : X ⟶ 𝔸ᴹ_S` factoring `f` and lift each `gⱼ` along the surjection
`i` induces on global sections to a `yⱼ` with `i⁻¹D(yⱼ) = X_{gⱼ}`. Pseudo-coherence of `Ri_*E` is
local on `𝔸ᴹ_S`, the opens `D(yⱼ)` cover the image of `i` because the `X_{gⱼ}` cover `X`, and
`Ri_*E` vanishes on the open complement of that image. On `D(yⱼ)` the restriction of `Ri_*E` is the
derived pushforward of `E|_{X_{gⱼ}}` along `i|_{D(yⱼ)}`, which is `m`-pseudo-coherent by
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_morphismRestrict_basicOpen`.

The intermediate scheme `T = Spec R[xᵢ, yᵢ, zᵢ]/(∑ yᵢzᵢ - 1)` of the source's proof does not
appear, and neither does the relation `1 = ∑ fᵢgᵢ`; see the implementation notes. -/
public theorem exists_isPseudoCoherentFromAfterPushforward_of_forall_basicOpen {X S : Scheme.{u}}
    [IsAffine X] [IsAffine S] (f : X ⟶ S) [LocallyOfFiniteType f]
    (hO : ∀ {a b : ℕ}
      (p : AffineSpace (ULift.{u} (Fin a)) S ⟶ AffineSpace (ULift.{u} (Fin b)) S)
      [IsClosedImmersion p],
      RingedSpace.IsPseudoCoherent (X := (AffineSpace (ULift.{u} (Fin b)) S).toRingedSpace)
        ((DerivedCategory.singleFunctor (AffineSpace (ULift.{u} (Fin b)) S).Modules 0).obj
          ((pushforward p).obj
            (SheafOfModules.unit (AffineSpace (ULift.{u} (Fin a)) S).ringCatSheaf))))
    (hOb : ∀ (N : ℕ) (a : Γ(AffineSpace (ULift.{u} (Fin N)) S, ⊤)),
      PushforwardStructureSheafPseudoCoherent S
        ((AffineSpace (ULift.{u} (Fin N)) S).basicOpen a).toScheme)
    (E : DerivedCategory X.Modules) (m : ℤ) {n : ℕ} (g : Fin n → Γ(X, ⊤))
    (hg : PrimeSpectrum.IsStandardOpenCoverOfSpectrum g)
    (h : ∀ j : Fin n, ∃ (k : ℕ) (l : (X.basicOpen (g j)).toScheme ⟶
        AffineSpace (ULift.{u} (Fin k)) S),
      IsClosedImmersion l ∧
        l ≫ (AffineSpace.over (ULift.{u} (Fin k)) S).hom = (X.basicOpen (g j)).ι ≫ f ∧
          IsPseudoCoherentFromAfterPushforward l
            ((restrictFunctor (X.basicOpen (g j)).ι).mapDerivedCategory.obj E) m) :
    ∃ (K : ℕ) (i : X ⟶ AffineSpace (ULift.{u} (Fin K)) S),
      IsClosedImmersion i ∧
        i ≫ (AffineSpace.over (ULift.{u} (Fin K)) S).hom = f ∧
          IsPseudoCoherentFromAfterPushforward i E m := by
  obtain ⟨M, i, hi, hiover⟩ := exists_isClosedImmersion_affineSpace f
  have := hi
  obtain ⟨y, hy⟩ : ∃ y : Fin n → Γ(AffineSpace (ULift.{u} (Fin M)) S, ⊤),
      ∀ j, i.appTop (y j) = g j := by
    choose y hy using fun j => i.app_surjective ⊤ (isAffineOpen_top _) (g j)
    exact ⟨y, hy⟩
  have hpre : ∀ j, i ⁻¹ᵁ ((AffineSpace (ULift.{u} (Fin M)) S).basicOpen (y j)) =
      X.basicOpen (g j) := by
    intro j
    rw [Scheme.preimage_basicOpen_top]
    exact congrArg X.basicOpen (hy j)
  have hcov : (⨆ j, X.basicOpen (g j)) = ⊤ :=
    (Scheme.isStandardOpenCoverOfSpectrum_iff_iSup_basicOpen_eq_top g).mp hg
  refine ⟨M, i, hi, hiover, ?_⟩
  rw [isPseudoCoherentFromAfterPushforward_iff]
  refine RingedSpace.isPseudoCoherentFrom_of_local_restrict
    (X := (AffineSpace (ULift.{u} (Fin M)) S).toRingedSpace) _ m fun x => ?_
  by_cases hx : x ∈ Set.range i.toLRSHom.toShHom.hom.base
  · obtain ⟨z, rfl⟩ := hx
    have hz : z ∈ (⨆ j, X.basicOpen (g j)) := by
      rw [hcov]
      exact Opens.mem_top z
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hz
    rw [← hpre j] at hj
    refine ⟨(AffineSpace (ULift.{u} (Fin M)) S).basicOpen (y j), hj, ?_⟩
    refine isPseudoCoherentFrom_derivedRestrictModules_of_morphismRestrict i _ E m ?_
    exact isPseudoCoherentFromAfterPushforward_morphismRestrict_basicOpen i f hiover (y j) hO
      (hOb M (y j)) E m (by rw [hpre j]; exact h j)
  · have hclosed := Stacks.ClosedImmersion.isClosedEmbedding_base_toShHom i
    let U : Opens (AffineSpace (ULift.{u} (Fin M)) S) :=
      ⟨(Set.range i.toLRSHom.toShHom.hom.base)ᶜ, hclosed.isClosed_range.isOpen_compl⟩
    have hbot : (Opens.map i.toLRSHom.toShHom.hom.base).obj U = ⊥ := by
      ext w
      simp [U]
    exact ⟨U, hx, RingedSpace.IsPseudoCoherentFrom.of_isZero
      (RingedSpace.isZero_derivedRestrict_derivedPushforward_of_preimage_eq_bot
        i.toLRSHom.toShHom U hclosed hbot E) m⟩

/-- **Stacks 09VE**, granted the side condition of Stacks 09VA. Let `f : X ⟶ S` be a morphism of
affine schemes locally of finite type, let `E` be an object of `D(𝒪_X)` and let the basic opens of
`g : Fin n → Γ(X, ⊤)` be a standard affine open cover of `X`. Then the equivalent conditions of
Stacks 09VC hold for every pair `(X_{gⱼ} ⟶ S, E|_{X_{gⱼ}})` if and only if they hold for the pair
`(X ⟶ S, E)`.

The implication from the cover to `X` is
`AlgebraicGeometry.Scheme.Modules.exists_isPseudoCoherentFromAfterPushforward_of_forall_basicOpen`
and the converse is the second paragraph of Stacks 09VD,
`AlgebraicGeometry.Scheme.Modules.exists_isPseudoCoherentFromAfterPushforward_basicOpen`.

No `stacks` attribute is placed: Stacks 09VE is stated with no hypotheses, whereas both halves here
carry the side condition of Stacks 09VA — `hOb` for the converse, and `hO` as well for the forward
implication. Both are asked for in exactly the shape those results use, so discharging the
side condition discharges them without restating anything. -/
public theorem isPseudoCoherentFrom_some_iff_forall_basicOpen {X S : Scheme.{u}}
    [IsAffine X] [IsAffine S] (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f]
    (hO : ∀ {a b : ℕ}
      (p : AffineSpace (ULift.{u} (Fin a)) S ⟶ AffineSpace (ULift.{u} (Fin b)) S)
      [IsClosedImmersion p],
      RingedSpace.IsPseudoCoherent (X := (AffineSpace (ULift.{u} (Fin b)) S).toRingedSpace)
        ((DerivedCategory.singleFunctor (AffineSpace (ULift.{u} (Fin b)) S).Modules 0).obj
          ((pushforward p).obj
            (SheafOfModules.unit (AffineSpace (ULift.{u} (Fin a)) S).ringCatSheaf))))
    (hOb : ∀ (N : ℕ) (a : Γ(AffineSpace (ULift.{u} (Fin N)) S, ⊤)),
      PushforwardStructureSheafPseudoCoherent S
        ((AffineSpace (ULift.{u} (Fin N)) S).basicOpen a).toScheme)
    (E : DerivedCategory X.Modules) (m : ℤ) {n : ℕ} (g : Fin n → Γ(X, ⊤))
    (hg : PrimeSpectrum.IsStandardOpenCoverOfSpectrum g) :
    (∀ j : Fin n, ∃ (k : ℕ) (i : (X.basicOpen (g j)).toScheme ⟶
        AffineSpace (ULift.{u} (Fin k)) S),
      IsClosedImmersion i ∧
        i ≫ (AffineSpace.over (ULift.{u} (Fin k)) S).hom = (X.basicOpen (g j)).ι ≫ f ∧
          IsPseudoCoherentFromAfterPushforward i
            ((restrictFunctor (X.basicOpen (g j)).ι).mapDerivedCategory.obj E) m) ↔
      (∃ (k : ℕ) (i : X ⟶ AffineSpace (ULift.{u} (Fin k)) S),
        IsClosedImmersion i ∧
          i ≫ (AffineSpace.over (ULift.{u} (Fin k)) S).hom = f ∧
            IsPseudoCoherentFromAfterPushforward i E m) :=
  ⟨exists_isPseudoCoherentFromAfterPushforward_of_forall_basicOpen f hO hOb E m g hg,
    fun h j => exists_isPseudoCoherentFromAfterPushforward_basicOpen f hOb E m (g j) h⟩

end AlgebraicGeometry.Scheme.Modules

end
