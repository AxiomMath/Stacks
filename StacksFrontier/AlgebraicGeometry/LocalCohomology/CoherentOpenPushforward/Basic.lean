module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Divisors.ReflexiveEquivalence.StalkDescent
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtale.Locality
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.NoetherianImmersion
public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic

/-!
# Coherence of a direct image along an open immersion, tested on the affine opens of the target

Let `j : U ⟶ X` be an open immersion with `X` locally Noetherian and let `G` be an `𝒪_U`-module.
Coherence of `j_* G` is a local condition on `X`, and restricting it to an open `V ⊆ X` computes
the direct image along the restricted morphism `j ∣_ V : j ⁻¹ᵁ V ⟶ V`. So `j_* G` is coherent as
soon as every `(j ∣_ V)_* (G|_{j ⁻¹ᵁ V})` is, for `V` running over the affine opens of `X`.

The second half of the file supplies the criterion this reduction is used with. On a locally
Noetherian scheme a quasi-coherent submodule of a coherent module is coherent
([Stacks, Tag 01Y1]), and `j_*` preserves monomorphisms because it is a right adjoint; so a
monomorphism `G ⟶ F` with `j_* F` coherent forces `j_* G` to be coherent. Combining the two,
coherence of `j_* G` follows from a monomorphism `G|_{j ⁻¹ᵁ V} ⟶ F|_{j ⁻¹ᵁ V}` over each affine
open `V` of `X` — monomorphisms which need not glue to one over `U`, and in general do not: for
`U = X` an elliptic curve, `F` a nontrivial degree-zero line bundle and `G = 𝒪_U` there is no
nonzero map `G ⟶ F` at all, while locally on `X` there is a monomorphism everywhere.

This is the shape in which [Stacks, Tag 0BJZ] concludes, in both directions of its equivalence:
the direct image of the structure sheaf of the reduced closure of an associated point is shown to
be coherent by embedding it, locally on the target, into the given coherent module. The last
statement here is that conclusion for the direct image of the structure sheaf of an arbitrary
closed subscheme of `U`, written at the composite immersion so that it matches the clause of
Tag 0BJZ verbatim.

## Main results

* `Stacks.AlgebraicGeometry.CoherentOpenPushforward.isCoherent_pushforward_of_forall_affineOpen` —
  coherence of `j_* G` is tested on the affine opens of `X`.
* `Stacks.AlgebraicGeometry.CoherentOpenPushforward.isCoherent_pushforward_of_mono` — a
  monomorphism into a module with coherent direct image gives a coherent direct image.
* `Stacks.AlgebraicGeometry.CoherentOpenPushforward.isCoherent_pushforward_of_isZero` — the
  complementary branch: the direct image of a zero module is coherent.
* `Stacks.AlgebraicGeometry.CoherentOpenPushforward.isCoherent_pushforward_of_affineLocal_mono` —
  the combination: monomorphisms over the affine opens of the target suffice.
* `Stacks.AlgebraicGeometry.CoherentOpenPushforward.isCoherent_pushforward_subscheme_of_mono` —
  the same for the structure sheaf of a closed subscheme of `U`, pushed forward along the
  composite of its immersion with `j`.

## Implementation notes

The coherence predicate used throughout is the one that dot notation on an `X.Modules` resolves
to, namely the root-namespace `SheafOfModules.IsCoherent`. The library carries a second class of
the same name and the same two fields, `Stacks.SheafOfModules.IsCoherent`; the results quoted
below (`Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_of_mono_of_isQuasicoherent`,
`Stacks.FundamentalGroup.ExtendedEtaleFold.isCoherent_of_isAffineOpen_restrict`,
`Stacks.AlgebraicGeometry.ReflexiveEquivalence.isCoherent_restrict` and
`Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso`) are all about the former, so no
bridge between the two is needed here.

The base-change isomorphism `restrictPushforwardIso` is stated as an isomorphism of composite
functors. Each use below names its value at the module with an explicit type ascription, so that
instance search sees the `.obj`-applied form rather than `(F ⋙ G).obj`, for which it does not
fire.

Quasi-coherence of the direct image along the closed immersion of a subscheme is supplied by
`AlgebraicGeometry.pushforward_isQuasicoherent` applied explicitly rather than by instance
search, which does not reach it through the two intervening `IsAffineHom`-style instances.

## References

* [Stacks Project, Tag 0BJZ](https://stacks.math.columbia.edu/tag/0BJZ)
* [Stacks Project, Tag 01Y1](https://stacks.math.columbia.edu/tag/01Y1)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Stacks.AlgebraicGeometry.AffinePushforward (restrictPushforwardIso)
open Stacks.AlgebraicGeometry.CoherentDevissage (isCoherent_of_iso)
open Stacks.AlgebraicGeometry.CoherentOfFiniteType (isCoherent_of_mono_of_isQuasicoherent)
open Stacks.AlgebraicGeometry.ReflexiveEquivalence (isCoherent_restrict)
open Stacks.FundamentalGroup.ExtendedEtaleFold (isCoherent_of_isAffineOpen_restrict)

universe u

namespace Stacks.AlgebraicGeometry.CoherentOpenPushforward

variable {U X : Scheme.{u}} (j : U ⟶ X)

/-- **Coherence of a direct image along an open immersion is tested on the affine opens of the
target.** Restriction to an open `V` of `X` turns `j_* G` into the direct image of `G|_{j ⁻¹ᵁ V}`
along `j ∣_ V`, and coherence on a locally Noetherian scheme is local on the affine opens. -/
theorem isCoherent_pushforward_of_forall_affineOpen [IsOpenImmersion j] [IsLocallyNoetherian X]
    (G : U.Modules)
    (h : ∀ V : X.Opens, IsAffineOpen V →
      ((Scheme.Modules.pushforward (j ∣_ V)).obj (G.restrict (j ⁻¹ᵁ V).ι)).IsCoherent) :
    ((Scheme.Modules.pushforward j).obj G).IsCoherent := by
  refine isCoherent_of_isAffineOpen_restrict _ fun V hV => ?_
  have e : ((Scheme.Modules.pushforward j).obj G).restrict V.ι ≅
      (Scheme.Modules.pushforward (j ∣_ V)).obj (G.restrict (j ⁻¹ᵁ V).ι) :=
    (restrictPushforwardIso j V).app G
  have := h V hV
  exact isCoherent_of_iso e

/-- **A quasi-coherent submodule with coherent ambient direct image has coherent direct image.**
The functor `j_*` is a right adjoint, so it preserves the monomorphism, and a quasi-coherent
submodule of a coherent module on a locally Noetherian scheme is coherent
([Stacks, Tag 01Y1]). -/
theorem isCoherent_pushforward_of_mono [IsOpenImmersion j] [IsLocallyNoetherian X]
    {G F : U.Modules} [G.IsQuasicoherent]
    (hF : ((Scheme.Modules.pushforward j).obj F).IsCoherent) (φ : G ⟶ F) [Mono φ] :
    ((Scheme.Modules.pushforward j).obj G).IsCoherent :=
  isCoherent_of_mono_of_isQuasicoherent hF ((Scheme.Modules.pushforward j).map φ)

/-- **The direct image of a zero module is coherent.** Direct image is additive, so it carries a
zero object to a zero object, and a zero module is coherent.

This is the complementary branch of the affine-local criterion below: over an affine open `V` of
`X` that misses the support of `G`, the restriction of `G` to `j ⁻¹ᵁ V` is zero and no
monomorphism into anything is needed. -/
theorem isCoherent_pushforward_of_isZero (f : U ⟶ X) (G : U.Modules) (hG : Limits.IsZero G) :
    ((Scheme.Modules.pushforward f).obj G).IsCoherent :=
  Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_isZero
    ((Scheme.Modules.pushforward f).map_isZero hG)

/-- **Monomorphisms over the affine opens of the target suffice.** If `j_* F` is coherent and
`G` embeds into `F` after restriction to `j ⁻¹ᵁ V` for every affine open `V` of `X`, then `j_* G`
is coherent. The embeddings are not required to be restrictions of a single monomorphism
`G ⟶ F`, which is what makes this usable: see the module documentation. -/
theorem isCoherent_pushforward_of_affineLocal_mono [IsOpenImmersion j] [IsLocallyNoetherian X]
    (G F : U.Modules) [G.IsQuasicoherent]
    (hF : ((Scheme.Modules.pushforward j).obj F).IsCoherent)
    (hmono : ∀ V : X.Opens, IsAffineOpen V →
      ∃ φ : G.restrict (j ⁻¹ᵁ V).ι ⟶ F.restrict (j ⁻¹ᵁ V).ι, Mono φ) :
    ((Scheme.Modules.pushforward j).obj G).IsCoherent := by
  refine isCoherent_pushforward_of_forall_affineOpen j G fun V hV => ?_
  have : IsLocallyNoetherian V.toScheme := isLocallyNoetherian_of_isOpenImmersion V.ι
  obtain ⟨φ, hφ⟩ := hmono V hV
  have := hφ
  have eF : ((Scheme.Modules.pushforward j).obj F).restrict V.ι ≅
      (Scheme.Modules.pushforward (j ∣_ V)).obj (F.restrict (j ⁻¹ᵁ V).ι) :=
    (restrictPushforwardIso j V).app F
  have hFV : ((Scheme.Modules.pushforward (j ∣_ V)).obj (F.restrict (j ⁻¹ᵁ V).ι)).IsCoherent :=
    have : (((Scheme.Modules.pushforward j).obj F).restrict V.ι).IsCoherent :=
      have := hF; isCoherent_restrict V _
    isCoherent_of_iso eF.symm
  exact isCoherent_pushforward_of_mono (j ∣_ V) hFV φ

/-- **The criterion in the shape [Stacks, Tag 0BJZ] uses it.** For a closed subscheme of `U`
given by an ideal sheaf `I`, the direct image of its structure sheaf along the composite
`I.subschemeι ≫ j` is coherent as soon as that direct image embeds into `F` over each affine
open of `X`, where `j_* F` is coherent.

Taking `I` to be the vanishing ideal of the closure of a point `x` of `U`, the conclusion is the
clause of Tag 0BJZ at `x`. -/
theorem isCoherent_pushforward_subscheme_of_mono [IsOpenImmersion j]
    [IsLocallyNoetherian X] (I : U.IdealSheafData) (F : U.Modules)
    (hF : ((Scheme.Modules.pushforward j).obj F).IsCoherent)
    (hmono : ∀ V : X.Opens, IsAffineOpen V →
      ∃ φ : ((Scheme.Modules.pushforward I.subschemeι).obj
            (SheafOfModules.unit I.subscheme.ringCatSheaf)).restrict (j ⁻¹ᵁ V).ι ⟶
          F.restrict (j ⁻¹ᵁ V).ι, Mono φ) :
    ((Scheme.Modules.pushforward (I.subschemeι ≫ j)).obj
      (SheafOfModules.unit I.subscheme.ringCatSheaf)).IsCoherent := by
  have hq : ((Scheme.Modules.pushforward I.subschemeι).obj
      (SheafOfModules.unit I.subscheme.ringCatSheaf)).IsQuasicoherent :=
    AlgebraicGeometry.pushforward_isQuasicoherent I.subschemeι _
  have e : (Scheme.Modules.pushforward j).obj
        ((Scheme.Modules.pushforward I.subschemeι).obj
          (SheafOfModules.unit I.subscheme.ringCatSheaf)) ≅
      (Scheme.Modules.pushforward (I.subschemeι ≫ j)).obj
        (SheafOfModules.unit I.subscheme.ringCatSheaf) :=
    (Scheme.Modules.pushforwardComp I.subschemeι j).app _
  have := isCoherent_pushforward_of_affineLocal_mono j _ F hF hmono
  exact isCoherent_of_iso e.symm

end Stacks.AlgebraicGeometry.CoherentOpenPushforward

end
