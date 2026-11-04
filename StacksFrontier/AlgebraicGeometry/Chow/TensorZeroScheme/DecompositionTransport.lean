module

public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.DecompositionBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.TotalSpaceComparison
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The diagram of Tag 0F97 and its two sections commute with arbitrary base change

Let `Y` be a scheme, let `L₁` and `L₂` be invertible `𝒪_Y`-modules, let `s` be a global section
of `L₁ ⊗_{𝒪_Y} L₂`, let `i : D → Y` be the zero scheme of `s` and let
`R : Stacks.Chow.TensorZeroScheme.Decomposition Y L₁ L₂ s` be a diagram as in [Stacks, Tag
0F97] — a scheme `p : L ⟶ Y`, two closed subschemes `D₁`, `D₂` of `L` over `D`, two sections
`s₁`, `s₂` of `p^*L₁`, `p^*L₂`, and the tag's seven numbered conditions.

This file proves the tag's final assertion: **the formation of the diagram and of the two
sections commutes with arbitrary base change.** For *any* morphism `g : Y' ⟶ Y` of schemes — no
flatness, no finiteness, no affineness — the transported data

* total space `L' = L ×_Y Y'`, with `p' : L' ⟶ Y'` the second projection,
* `D₁' = h^{-1}D₁` and `D₂' = h^{-1}D₂`, where `h : L' ⟶ L` is the first projection,
* `s₁' = h^*s₁` and `s₂' = h^*s₂`, read in `(p')^*(g^*Lᵢ)` through the comparison
  `Stacks.Chow.TensorZeroScheme.squarePullbackMap` of the square `h ≫ p = p' ≫ g`,

is again a diagram as in the tag, for the base-changed section `g^*s` of `g^*L₁ ⊗ g^*L₂` and the
base-changed zero scheme. That is exactly
`Stacks.Chow.TensorZeroScheme.Decomposition.IsStableUnderBaseChange`, which this file inhabits.

## Main definitions

* `Stacks.Chow.TensorZeroScheme.squarePullbackIso`: the comparison
  `Stacks.Chow.TensorZeroScheme.squarePullbackMap` as an isomorphism.
* `Stacks.Chow.TensorZeroScheme.baseChangeSection`: the transport of a global section of `f^*M`
  across a commutative square.
* `Stacks.Chow.TensorZeroScheme.branchSituationBaseChangeModuleIso`: the comparison
  `δ^*(L_j^{⊗ -1}|_D) ≅ (g^*L_j)^{⊗ -1}|_{D'}` of the modules of the two branch line bundles,
  where `δ : D' ⟶ D` is the canonical morphism of zero schemes.
* `Stacks.Chow.TensorZeroScheme.bcProj`: the projection `Dᵢ' ⟶ D'` of the base-changed diagram.
* `Stacks.Chow.TensorZeroScheme.bcBranchIso`: **condition (4) for the base-changed diagram**, the
  inverse image of a branch presented as a line bundle over `D'`.
* `Stacks.Chow.TensorZeroScheme.Decomposition.baseChange`: **the base-changed diagram**, as a
  `Decomposition` over `Y'` for an arbitrary cartesian square over `R.p` and `g`.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.isPullback_subschemeMap_of_comap`: **the closed
  subscheme cut out by an inverse-image ideal is the fibre product** of the closed subscheme with
  the morphism.
* `Stacks.Chow.TensorZeroScheme.comap_zeroIdeal_of_tensorSection_eq`: `q^{-1}D` is the zero
  scheme of a product of two sections whose product is `q^*s` — the statement of which
  `Stacks.Chow.TensorZeroScheme.comap_zeroIdeal_proj` is the instance at the construction.
* `Stacks.Chow.TensorZeroScheme.Decomposition.isStableUnderBaseChange`: **[Stacks, Tag 0F97],
  the base-change clause**: every diagram as in the tag is stable under arbitrary base change.

## Implementation notes

*Why the base-changed diagram is a transport and not a second construction.* The clause
`Decomposition.IsStableUnderBaseChange` pins its witness down completely: the total space is
required to be the fibre product, the two closed subschemes the inverse images and the two
sections the pullbacks. So the only thing to prove is that the transported data satisfies the
tag's seven conditions, and that is done here for an arbitrary diagram `R`, not only for the one
`Stacks.Chow.TensorZeroScheme.decompositionOfClauses` builds. Nothing about the construction —
in particular nothing about the fibre coordinates `coord₁`, `coord₂` out of which the sections
of the construction are made — enters.

*The two branches are presented as zero schemes.* `Decomposition.baseChange` takes its `D₁` to
be the zero scheme of `s₁'` rather than `h^{-1}D₁`, the two being equal by condition (3) for `R`
together with [Stacks, Tag 0B6Y]. That choice makes conditions (3) and (5) free of any transport
along an equality of ideal sheaves: condition (3) holds by `rfl`, and the regularity input of
condition (5) is `Stacks.LineBundle.isRegularSection_restrict_of_inf_eq_zeroSection` read at the
very subscheme the general theorem
`Stacks.Divisors.zeroScheme_tensorSection_eq_inf` asks for. The identity
`D₁' = h^{-1}D₁` the clause requires is then supplied as a proposition rather than built into
the data, which is what keeps every `Eq.rec` in this file at a variable.

*Where each condition comes from.* Condition (1) is
`Stacks.PullbackTensorIso.pullbackTensorSection_of_square`, the compatibility of [Stacks, Tag
01CD] with a commutative square. Condition (2) is the stability of locally-of-finite-type,
quasi-compactness, flatness and relative dimension one under base change, the last being
`AlgebraicGeometry.RelativeDimension.of_isPullback`. Condition (3) is [Stacks, Tag 0B6Y]
(`Stacks.Divisors.zeroScheme_pullback`) and the invariance of a zero scheme under an isomorphism
of modules. Conditions (4), (6) and (7) all rest on one cartesian square: the inverse image of a
closed subscheme of `L` is its fibre product with `L'`, and pasting that with the square over
`g` and with `D' = D ×_Y Y'` presents `h^{-1}D₁` as `D₁ ×_D D'`. Condition (4) then combines the
base change of the total space of a line bundle,
`Stacks.LineBundle.Situation.isPullback_baseChange`, with
`Stacks.LineBundle.Situation.totalSpaceIsoOfIso` for the comparison of the two modules;
condition (6) is the stability of isomorphisms under base change; and condition (7) is the
compatibility of the zero section with both of those,
`Stacks.LineBundle.Situation.zeroSection_comp_baseChangeToTotalSpace` and
`Stacks.LineBundle.Situation.zeroSection_comp_totalSpaceIsoOfIso_hom`. Condition (5) is derived
from conditions (1), (3), (4), (6) and (7) for the base-changed diagram and does not use
condition (5) for `R`.

*The comparison of the two branch modules.* `(branchSituation Y L₁ L₂ s L₂)` carries
`i^*(L₂^{⊗ -1})` and the base-changed one carries `(i')^*((g^*L₂)^{⊗ -1})`. The comparison is
the square `δ ≫ i = i' ≫ g` read through [Stacks, Tag 01CD] followed by the base change of the
inverse `Stacks.LineBundle.inverseSituationPullbackIso`. Only the *existence* of that last
isomorphism is used; no description of it on sections is needed, which is why this route does
not wait on the fibre coordinate of a line bundle being compatible with base change.

*Transparency.* The projections `.X`, `.L`, `.totalSpace` and `.zeroSection` of a
`Stacks.LineBundle.Situation` agree with their values only at default transparency, so every
step touching them is a term and not a `rw`; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.InverseSituationBaseChange`.

## References

* [Stacks Project, Tag 0F97](https://stacks.math.columbia.edu/tag/0F97)
* [Stacks Project, Tag 0F96](https://stacks.math.columbia.edu/tag/0F96)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01M2](https://stacks.math.columbia.edu/tag/01M2)
* [Stacks Project, Tag 02NJ](https://stacks.math.columbia.edu/tag/02NJ)
* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.PullbackTensorIso (pullbackTensorSection)

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- **The closed subscheme cut out by an inverse-image ideal is a fibre product.** If `K` is the
inverse image of `K` along `k : T' ⟶ T`, then the square whose horizontals are the two closed
immersions and whose verticals are `k` and the induced morphism is cartesian. The inverse image
is taken as a hypothesis rather than written into the statement, so that the lemma applies to
any ideal sheaf *equal* to it with no transport. -/
@[ega "I 4.4.1" "closed case", ega "III 2.6.2.3" "partial"]
theorem isPullback_subschemeMap_of_comap {T T' : Scheme.{u}} (k : T' ⟶ T)
    {I : T.IdealSheafData} {K : T'.IdealSheafData} (hK : I.comap k = K) :
    IsPullback K.subschemeι
      (subschemeMap K I k (le_map_iff_comap_le.2 hK.le)) k I.subschemeι :=
  AlgebraicGeometry.isPullback_of_isClosedImmersion _ _ _ _
    (subschemeMap_subschemeι _ _ _ _).symm
    (by rw [ker_subschemeι, ker_subschemeι]; exact hK)

end AlgebraicGeometry.Scheme.IdealSheafData

namespace Stacks.Chow.TensorZeroScheme

/-! ### Reading a morphism into a second presentation of a fibre product

Every statement in this section is about plain schemes and morphisms. That is deliberate: the
projections of a `Stacks.LineBundle.Situation` agree with their values only at default
transparency, so a `rw` inside a goal mentioning them is rejected with an ill-typed motive. The
specializations below are therefore `exact` applications of these lemmas, which cross the
transparency barrier for free. -/

section PullbackComparison

variable {A B Z P P' Q : Scheme.{u}} {u : P ⟶ A} {v : P ⟶ B} {f : A ⟶ Z} {g : B ⟶ Z}
  {u' : P' ⟶ A} {v' : P' ⟶ B} {vQ : Q ⟶ B}
  (hP : IsPullback u v f g) (hP' : IsPullback u' v' f g) (Θ : Q ≅ P')

/-- **The comparison of two presentations of a fibre product, corrected by an isomorphism of the
apex of the second, is a morphism over `B`.** -/
theorem isoIsPullback_trans_symm_hom_comp_snd (hΘ : Θ.hom ≫ v' = vQ) :
    (hP.isoIsPullback A B hP' ≪≫ Θ.symm).hom ≫ vQ = v := by
  rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, ← hΘ, Iso.inv_hom_id_assoc]
  exact hP.isoIsPullback_hom_snd A B hP'

/-- **The same comparison, read over `A` after undoing the isomorphism of the apex.** -/
theorem isoIsPullback_trans_symm_hom_comp_fst :
    (hP.isoIsPullback A B hP' ≪≫ Θ.symm).hom ≫ Θ.hom ≫ u' = u := by
  rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
  exact hP.isoIsPullback_hom_fst A B hP'

/-- **A morphism into a fibre product factors through a given section of its projection to `B`
as soon as its two components say so.** Here `o : B ⟶ Q` is the section, read in the second
presentation as `oP` and composed into `A` as `oA`; the hypotheses are that `c` agrees with
`z ≫ oA` over `A` and that the component of `c` over `B` is `z`. -/
theorem comp_isoIsPullback_trans_symm_hom {W : Scheme.{u}} (o : B ⟶ Q) {oP : B ⟶ P'}
    {oA : B ⟶ A} (hoΘ : o ≫ Θ.hom = oP) (hoP : oP ≫ v' = 𝟙 B) (hoA : oP ≫ u' = oA)
    (c : W ⟶ P) (z : W ⟶ B) (h₁ : c ≫ u = z ≫ oA) (h₂ : c ≫ v = z) :
    c ≫ (hP.isoIsPullback A B hP' ≪≫ Θ.symm).hom = z ≫ o := by
  refine (cancel_mono Θ.hom).mp ?_
  rw [Category.assoc, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id, Category.assoc, hoΘ]
  refine hP'.hom_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, hP.isoIsPullback_hom_fst A B hP', hoA]
    exact h₁
  · rw [Category.assoc, Category.assoc, hP.isoIsPullback_hom_snd A B hP', hoP, Category.comp_id]
    exact h₂

end PullbackComparison

/-- **A cartesian square stays cartesian when the corner opposite the base is moved by an
isomorphism.** -/
theorem isPullback_comp_isIso {A A' B Z P : Scheme.{u}} {u : P ⟶ A} {v : P ⟶ B} {f : A ⟶ Z}
    {g : B ⟶ Z} (hP : IsPullback u v f g) (e : A ≅ A') {f' : A' ⟶ Z}
    (he : e.hom ≫ f' = f) : IsPullback (u ≫ e.hom) v f' g := by
  have hiso : IsPullback e.hom f f' (𝟙 Z) :=
    IsPullback.of_horiz_isIso ⟨he.trans (Category.comp_id f).symm⟩
  have h := hP.paste_horiz hiso
  rwa [Category.comp_id] at h

/-- **The inclusions of two closed subschemes into a third commute with the inverse images of
all three.** -/
theorem subschemeMap_inclusion_comm {T T' : Scheme.{u}} (c : T' ⟶ T) {I J : T.IdealSheafData}
    {I' J' : T'.IdealSheafData} (hI : I.comap c = I') (hJ : J.comap c = J') (hIJ : I ≤ J)
    (hIJ' : I' ≤ J') :
    Scheme.IdealSheafData.inclusion hIJ' ≫ Scheme.IdealSheafData.subschemeMap I' I c
          (Scheme.IdealSheafData.le_map_iff_comap_le.2 hI.le) =
      Scheme.IdealSheafData.subschemeMap J' J c
          (Scheme.IdealSheafData.le_map_iff_comap_le.2 hJ.le) ≫
        Scheme.IdealSheafData.inclusion hIJ := by
  refine (cancel_mono I.subschemeι).mp ?_
  simp only [Category.assoc, Scheme.IdealSheafData.subschemeMap_subschemeι,
    Scheme.IdealSheafData.inclusion_subschemeι, Scheme.IdealSheafData.inclusion_subschemeι_assoc]

/-! ### The comparison of a commutative square, as an isomorphism and on sections -/

section Square

variable {A B A' B' : Scheme.{u}} {f : A ⟶ B} {g : B' ⟶ B} {f' : A' ⟶ B'} {h : A' ⟶ A}

/-- **The comparison `Stacks.Chow.TensorZeroScheme.squarePullbackMap` as an isomorphism**: each
of its three factors is a component of a natural isomorphism. -/
def squarePullbackIso (w : h ≫ f = f' ≫ g) (M : B.Modules) :
    (Scheme.Modules.pullback h).obj ((Scheme.Modules.pullback f).obj M) ≅
      (Scheme.Modules.pullback f').obj ((Scheme.Modules.pullback g).obj M) :=
  (Scheme.Modules.pullbackComp h f).app M ≪≫ (Scheme.Modules.pullbackCongr w).app M ≪≫
    ((Scheme.Modules.pullbackComp f' g).app M).symm

/-- The isomorphism is the comparison. -/
theorem squarePullbackIso_hom (w : h ≫ f = f' ≫ g) (M : B.Modules) :
    (squarePullbackIso w M).hom = squarePullbackMap w M := rfl

/-- **The transport of a global section of `f^*M` across a commutative square**: pull it back
along the upper edge and read the result through the comparison of [Stacks, Tag 01CD]. This is
the section the base-change clause of [Stacks, Tag 0F97] compares against. -/
def baseChangeSection (w : h ≫ f = f' ≫ g) (M : B.Modules)
    (a : Γ((Scheme.Modules.pullback f).obj M, ⊤)) :
    Γ((Scheme.Modules.pullback f').obj ((Scheme.Modules.pullback g).obj M), ⊤) :=
  Scheme.Modules.Hom.app (squarePullbackMap w M) ⊤
    (AlgebraicGeometry.pullbackGlobalSections h ((Scheme.Modules.pullback f).obj M) a)

/-- **The zero scheme of a section of a pulled-back invertible module commutes with base
change.** For a commutative square `c ≫ q = q' ≫ g` and a global section `a` of `q^*N`, the
inverse image along `c` of the zero scheme of `a` is the zero scheme of the transport of `a`
across the square. This is [Stacks, Tag 0B6Y] followed by the invariance of a zero scheme under
an isomorphism of modules. -/
theorem comap_zeroScheme_baseChange {V V' W W' : Scheme.{u}} {q : V ⟶ W} {g : W' ⟶ W}
    {q' : V' ⟶ W'} {c : V' ⟶ V} (w : c ≫ q = q' ≫ g) (N : W.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible W.sheaf.obj W.ringCatSheaf.property N]
    [AlgebraicGeometry.SheafOfModules.IsInvertible V.sheaf.obj V.ringCatSheaf.property
      ((Scheme.Modules.pullback q).obj N)]
    [AlgebraicGeometry.SheafOfModules.IsInvertible W'.sheaf.obj W'.ringCatSheaf.property
      ((Scheme.Modules.pullback g).obj N)]
    [AlgebraicGeometry.SheafOfModules.IsInvertible V'.sheaf.obj V'.ringCatSheaf.property
      ((Scheme.Modules.pullback q').obj ((Scheme.Modules.pullback g).obj N))]
    (a : Γ((Scheme.Modules.pullback q).obj N, ⊤)) :
    (Stacks.Divisors.zeroScheme V ((Scheme.Modules.pullback q).obj N) a).comap c =
      Stacks.Divisors.zeroScheme V'
        ((Scheme.Modules.pullback q').obj ((Scheme.Modules.pullback g).obj N))
        (baseChangeSection w N a) := by
  let : AlgebraicGeometry.SheafOfModules.IsInvertible V'.sheaf.obj V'.ringCatSheaf.property
      ((Scheme.Modules.pullback c).obj ((Scheme.Modules.pullback q).obj N)) :=
    Stacks.Divisors.pullback_isInvertible _ _
  refine (Stacks.Divisors.zeroScheme_pullback c
    ((Scheme.Modules.pullback q).obj N) a).symm.trans ?_
  exact AlgebraicGeometry.zeroScheme_eq_of_iso (squarePullbackIso w N) rfl

end Square

/-! ### The inverse image of `D` as a zero scheme -/

section ZeroIdeal

variable {Y : Scheme.{u}} {L₁ L₂ : Y.Modules}
  [h₁ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₁]
  [h₂ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₂]
  (s : Γ(Stacks.Divisors.tensorModules L₁ L₂, ⊤))

include h₁ h₂ in
/-- **The scheme-theoretic inverse image `q^{-1}D` is the zero scheme of any product of two
sections that `q^*s` factors as.** The zero scheme of a section commutes with pullback
([Stacks, Tag 0B6Y]) and the comparison of [Stacks, Tag 01CD] identifies `q^*(L₁ ⊗ L₂)` with
`q^*L₁ ⊗ q^*L₂` carrying `q^*s` to the reading of it used in [Stacks, Tag 0F97](1). -/
theorem comap_zeroIdeal_of_tensorSection_eq {T : Scheme.{u}} (q : T ⟶ Y)
    (a : Γ((Scheme.Modules.pullback q).obj L₁, ⊤))
    (b : Γ((Scheme.Modules.pullback q).obj L₂, ⊤))
    (hab : pullbackTensorSection q L₁ L₂ s =
      Stacks.Divisors.tensorSection ((Scheme.Modules.pullback q).obj L₁)
        ((Scheme.Modules.pullback q).obj L₂) ⊤ a b) :
    (zeroIdeal Y L₁ L₂ s).comap q =
      Stacks.Divisors.zeroScheme T
        (Stacks.Divisors.tensorModules ((Scheme.Modules.pullback q).obj L₁)
          ((Scheme.Modules.pullback q).obj L₂))
        (Stacks.Divisors.tensorSection ((Scheme.Modules.pullback q).obj L₁)
          ((Scheme.Modules.pullback q).obj L₂) ⊤ a b) := by
  let : AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property
      ((Scheme.Modules.pullback q).obj (Stacks.Divisors.tensorModules L₁ L₂)) :=
    Stacks.Divisors.pullback_isInvertible _ _
  refine ((Stacks.Divisors.zeroScheme_pullback q
    (Stacks.Divisors.tensorModules L₁ L₂) s).symm.trans ?_)
  refine (AlgebraicGeometry.zeroScheme_eq_of_iso
    (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso q L₁ L₂)
    (t := pullbackTensorSection q L₁ L₂ s) rfl).trans ?_
  exact congrArg (fun t => Stacks.Divisors.zeroScheme T
    (Stacks.Divisors.tensorModules ((Scheme.Modules.pullback q).obj L₁)
      ((Scheme.Modules.pullback q).obj L₂)) t) hab

end ZeroIdeal

/-! ### The comparison of the two branch line bundles' modules -/

section BranchModule

variable {Y Y' : Scheme.{u}} {L₁ L₂ : Y.Modules}
  [h₁ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₁]
  [h₂ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₂]
  (s : Γ(Stacks.Divisors.tensorModules L₁ L₂, ⊤)) (g : Y' ⟶ Y)

include h₁ h₂ in
/-- **The modules of the two branch line bundles correspond across the base change**:
`δ^*(N^{⊗ -1}|_D) ≅ (g^*N)^{⊗ -1}|_{D'}`, where `δ : D' ⟶ D` is the canonical morphism of zero
schemes. The square `δ ≫ i = i' ≫ g` read through [Stacks, Tag 01CD], followed by the base
change of the inverse. -/
def branchSituationBaseChangeModuleIso (N : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property N] :
    (Scheme.Modules.pullback (zeroIdealBaseChangeMap s g)).obj
        (branchSituation Y L₁ L₂ s N).L ≅
      (branchSituation Y' ((Scheme.Modules.pullback g).obj L₁)
        ((Scheme.Modules.pullback g).obj L₂) (pullbackTensorSection g L₁ L₂ s)
        ((Scheme.Modules.pullback g).obj N)).L :=
  squarePullbackIso (zeroIdealBaseChangeMap_comp_subschemeι s g) (inverseModule Y N) ≪≫
    (Scheme.Modules.pullback
        (zeroIdeal Y' ((Scheme.Modules.pullback g).obj L₁)
          ((Scheme.Modules.pullback g).obj L₂)
          (pullbackTensorSection g L₁ L₂ s)).subschemeι).mapIso
      (Stacks.LineBundle.inverseSituationPullbackIso g N)

end BranchModule

/-! ### The transport of one branch of the diagram -/

section BranchTransport

variable {Y Y' : Scheme.{u}} {L₁ L₂ : Y.Modules}
  [h₁ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₁]
  [h₂ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₂]
  {s : Γ(Stacks.Divisors.tensorModules L₁ L₂, ⊤)} (g : Y' ⟶ Y)
  [i₁ : AlgebraicGeometry.SheafOfModules.IsInvertible Y'.sheaf.obj Y'.ringCatSheaf.property
    ((Scheme.Modules.pullback g).obj L₁)]
  [i₂ : AlgebraicGeometry.SheafOfModules.IsInvertible Y'.sheaf.obj Y'.ringCatSheaf.property
    ((Scheme.Modules.pullback g).obj L₂)]
  {T T' : Scheme.{u}} {q : T ⟶ Y} {k : T' ⟶ T} {p' : T' ⟶ Y'}
  {Dᵢ : T.IdealSheafData} {K : T'.IdealSheafData}

include h₁ h₂ in
/-- **The projection `Dᵢ' ⟶ D'` of the base-changed diagram**: the morphism to `Y'` out of the
inverse image of `Dᵢ`, lifted through the cartesian square `D' = D ×_Y Y'`. -/
def bcProj (hsq : IsPullback k p' q g) (pᵢ : Dᵢ.subscheme ⟶ (zeroIdeal Y L₁ L₂ s).subscheme)
    (comm : Dᵢ.subschemeι ≫ q = pᵢ ≫ (zeroIdeal Y L₁ L₂ s).subschemeι)
    (hK : Dᵢ.comap k = K) :
    K.subscheme ⟶ (zeroIdeal Y' ((Scheme.Modules.pullback g).obj L₁)
      ((Scheme.Modules.pullback g).obj L₂) (pullbackTensorSection g L₁ L₂ s)).subscheme :=
  (isPullback_zeroIdealBaseChangeMap s g).lift (K.subschemeι ≫ p')
    ((Scheme.IdealSheafData.subschemeMap K Dᵢ k
      (Scheme.IdealSheafData.le_map_iff_comap_le.2 hK.le)) ≫ pᵢ)
    (by
      rw [Category.assoc, ← hsq.w, Category.assoc, ← comm,
        ← Category.assoc _ Dᵢ.subschemeι q, Scheme.IdealSheafData.subschemeMap_subschemeι,
        Category.assoc])

include h₁ h₂ in
/-- **The left-hand square of the base-changed diagram commutes.** -/
theorem bcProj_comp_subschemeι (hsq : IsPullback k p' q g)
    (pᵢ : Dᵢ.subscheme ⟶ (zeroIdeal Y L₁ L₂ s).subscheme)
    (comm : Dᵢ.subschemeι ≫ q = pᵢ ≫ (zeroIdeal Y L₁ L₂ s).subschemeι)
    (hK : Dᵢ.comap k = K) :
    K.subschemeι ≫ p' = bcProj g hsq pᵢ comm hK ≫ (zeroIdeal Y' ((Scheme.Modules.pullback g).obj L₁)
      ((Scheme.Modules.pullback g).obj L₂) (pullbackTensorSection g L₁ L₂ s)).subschemeι :=
  ((isPullback_zeroIdealBaseChangeMap s g).lift_fst _ _ _).symm

include h₁ h₂ in
/-- **The projection of the base-changed diagram lies over the projection of the given one.** -/
@[reassoc]
theorem bcProj_comp_zeroIdealBaseChangeMap (hsq : IsPullback k p' q g)
    (pᵢ : Dᵢ.subscheme ⟶ (zeroIdeal Y L₁ L₂ s).subscheme)
    (comm : Dᵢ.subschemeι ≫ q = pᵢ ≫ (zeroIdeal Y L₁ L₂ s).subschemeι)
    (hK : Dᵢ.comap k = K) :
    bcProj g hsq pᵢ comm hK ≫ zeroIdealBaseChangeMap s g =
      (Scheme.IdealSheafData.subschemeMap K Dᵢ k
      (Scheme.IdealSheafData.le_map_iff_comap_le.2 hK.le)) ≫ pᵢ :=
  (isPullback_zeroIdealBaseChangeMap s g).lift_snd _ _ _

include h₁ h₂ in
/-- **The inverse image of a closed subscheme of `L` over `D` is its fibre product with `D'`
over `D`.** The square over `g` and the cartesian square `D' = D ×_Y Y'` are pasted and the
latter cancelled. -/
theorem isPullback_over_zeroIdealBaseChangeMap (hsq : IsPullback k p' q g)
    (hK : Dᵢ.comap k = K) (a : Dᵢ.subscheme ⟶ (zeroIdeal Y L₁ L₂ s).subscheme)
    (b : K.subscheme ⟶ (zeroIdeal Y' ((Scheme.Modules.pullback g).obj L₁)
      ((Scheme.Modules.pullback g).obj L₂) (pullbackTensorSection g L₁ L₂ s)).subscheme)
    (ha : Dᵢ.subschemeι ≫ q = a ≫ (zeroIdeal Y L₁ L₂ s).subschemeι)
    (hb : K.subschemeι ≫ p' = b ≫ (zeroIdeal Y' ((Scheme.Modules.pullback g).obj L₁)
      ((Scheme.Modules.pullback g).obj L₂) (pullbackTensorSection g L₁ L₂ s)).subschemeι)
    (hab : (Scheme.IdealSheafData.subschemeMap K Dᵢ k
      (Scheme.IdealSheafData.le_map_iff_comap_le.2 hK.le)) ≫ a = b ≫ zeroIdealBaseChangeMap s g) :
    IsPullback (Scheme.IdealSheafData.subschemeMap K Dᵢ k
      (Scheme.IdealSheafData.le_map_iff_comap_le.2 hK.le)) b a (zeroIdealBaseChangeMap s g) := by
  refine IsPullback.of_bot ?_ hab (isPullback_zeroIdealBaseChangeMap s g).flip
  have hpaste :=
    (Scheme.IdealSheafData.isPullback_subschemeMap_of_comap k hK).flip.paste_vert hsq
  rw [hb, ha] at hpaste
  exact hpaste

include h₁ h₂ in
/-- **The inverse image of `Dᵢ` is `Dᵢ ×_D D'`.** -/
theorem isPullback_bcProj (hsq : IsPullback k p' q g)
    (pᵢ : Dᵢ.subscheme ⟶ (zeroIdeal Y L₁ L₂ s).subscheme)
    (comm : Dᵢ.subschemeι ≫ q = pᵢ ≫ (zeroIdeal Y L₁ L₂ s).subschemeι)
    (hK : Dᵢ.comap k = K) :
    IsPullback (Scheme.IdealSheafData.subschemeMap K Dᵢ k
      (Scheme.IdealSheafData.le_map_iff_comap_le.2 hK.le)) (bcProj g hsq pᵢ comm hK) pᵢ
      (zeroIdealBaseChangeMap s g) :=
  isPullback_over_zeroIdealBaseChangeMap g hsq hK pᵢ (bcProj g hsq pᵢ comm hK) comm
    (bcProj_comp_subschemeι g hsq pᵢ comm hK)
    (bcProj_comp_zeroIdealBaseChangeMap g hsq pᵢ comm hK).symm

include h₁ h₂ in
/-- The invertibility of the module of the base-changed branch bundle, read on the scheme of the
base-changed situation. Instance search does not find it: that scheme is `D'` only after the
situation is unfolded. -/
theorem isInvertible_branchSituation_baseChange (N : Y.Modules)
    [_hN : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property N]
    [hN' : AlgebraicGeometry.SheafOfModules.IsInvertible Y'.sheaf.obj Y'.ringCatSheaf.property
      ((Scheme.Modules.pullback g).obj N)] :
    AlgebraicGeometry.SheafOfModules.IsInvertible
      ((branchSituation Y L₁ L₂ s N).baseChange (zeroIdealBaseChangeMap s g)).X.sheaf.obj
      ((branchSituation Y L₁ L₂ s N).baseChange
        (zeroIdealBaseChangeMap s g)).X.ringCatSheaf.property
      (branchSituation Y' ((Scheme.Modules.pullback g).obj L₁)
      ((Scheme.Modules.pullback g).obj L₂) (pullbackTensorSection g L₁ L₂ s)
      ((Scheme.Modules.pullback g).obj N)).L :=
  Stacks.LineBundle.Situation.invertible (branchSituation Y' ((Scheme.Modules.pullback g).obj L₁)
      ((Scheme.Modules.pullback g).obj L₂) (pullbackTensorSection g L₁ L₂ s)
      ((Scheme.Modules.pullback g).obj N))

include h₁ h₂ in
/-- **Tag 0F97(4) for the base-changed diagram**: the inverse image of a branch presented as the
line bundle `Spec_D(Sym(N^{⊗ -1}|_D))` is the line bundle
`Spec_{D'}(Sym((g^*N)^{⊗ -1}|_{D'}))`. The inverse image is `Dᵢ ×_D D'`, the base change of
the total space of a line bundle is a fibre product too, and the two modules are compared by
`Stacks.Chow.TensorZeroScheme.branchSituationBaseChangeModuleIso`. -/
def bcBranchIso (hsq : IsPullback k p' q g) (pᵢ : Dᵢ.subscheme ⟶ (zeroIdeal Y L₁ L₂ s).subscheme)
    (comm : Dᵢ.subschemeι ≫ q = pᵢ ≫ (zeroIdeal Y L₁ L₂ s).subschemeι)
    (hK : Dᵢ.comap k = K) (N : Y.Modules)
    [hN : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property N]
    [hN' : AlgebraicGeometry.SheafOfModules.IsInvertible Y'.sheaf.obj Y'.ringCatSheaf.property
      ((Scheme.Modules.pullback g).obj N)]
    (e : Dᵢ.subscheme ≅ (branchSituation Y L₁ L₂ s N).totalSpace)
    (he : e.hom ≫ (branchSituation Y L₁ L₂ s N).totalSpaceToBase = pᵢ) :
    K.subscheme ≅ (branchSituation Y' ((Scheme.Modules.pullback g).obj L₁)
      ((Scheme.Modules.pullback g).obj L₂) (pullbackTensorSection g L₁ L₂ s)
      ((Scheme.Modules.pullback g).obj N)).totalSpace :=
  haveI := isInvertible_branchSituation_baseChange (s := s) g N
  (isPullback_comp_isIso (isPullback_bcProj g hsq pᵢ comm hK) e he).isoIsPullback _ _
      ((branchSituation Y L₁ L₂ s N).isPullback_baseChange (zeroIdealBaseChangeMap s g)) ≪≫
    (((branchSituation Y L₁ L₂ s N).baseChange (zeroIdealBaseChangeMap s g)).totalSpaceIsoOfIso
      (branchSituation Y' ((Scheme.Modules.pullback g).obj L₁)
        ((Scheme.Modules.pullback g).obj L₂) (pullbackTensorSection g L₁ L₂ s)
        ((Scheme.Modules.pullback g).obj N)).L
      (branchSituationBaseChangeModuleIso s g N)).symm

include h₁ h₂ in
/-- **Tag 0F97(4) for the base-changed diagram, as an identification over `D'`.** -/
theorem bcBranchIso_hom_comp_totalSpaceToBase (hsq : IsPullback k p' q g)
    (pᵢ : Dᵢ.subscheme ⟶ (zeroIdeal Y L₁ L₂ s).subscheme)
    (comm : Dᵢ.subschemeι ≫ q = pᵢ ≫ (zeroIdeal Y L₁ L₂ s).subschemeι)
    (hK : Dᵢ.comap k = K) (N : Y.Modules)
    [hN : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property N]
    [hN' : AlgebraicGeometry.SheafOfModules.IsInvertible Y'.sheaf.obj Y'.ringCatSheaf.property
      ((Scheme.Modules.pullback g).obj N)]
    (e : Dᵢ.subscheme ≅ (branchSituation Y L₁ L₂ s N).totalSpace)
    (he : e.hom ≫ (branchSituation Y L₁ L₂ s N).totalSpaceToBase = pᵢ) :
    (bcBranchIso g hsq pᵢ comm hK N e he).hom ≫
        (branchSituation Y' ((Scheme.Modules.pullback g).obj L₁)
          ((Scheme.Modules.pullback g).obj L₂) (pullbackTensorSection g L₁ L₂ s)
          ((Scheme.Modules.pullback g).obj N)).totalSpaceToBase =
      bcProj g hsq pᵢ comm hK :=
  have := isInvertible_branchSituation_baseChange (s := s) g N
  isoIsPullback_trans_symm_hom_comp_snd
    (isPullback_comp_isIso (isPullback_bcProj g hsq pᵢ comm hK) e he)
    ((branchSituation Y L₁ L₂ s N).isPullback_baseChange (zeroIdealBaseChangeMap s g)) _
    (((branchSituation Y L₁ L₂ s N).baseChange
      (zeroIdealBaseChangeMap s g)).totalSpaceIsoOfIso_hom_comp_totalSpaceToBase _ _)

include h₁ h₂ in
/-- **A morphism into the base-changed branch factors through its zero section** as soon as it
does so after the identification of the given branch with its line bundle, and its component
over `D'` is the given morphism. -/
theorem comp_bcBranchIso_hom (hsq : IsPullback k p' q g)
    (pᵢ : Dᵢ.subscheme ⟶ (zeroIdeal Y L₁ L₂ s).subscheme)
    (comm : Dᵢ.subschemeι ≫ q = pᵢ ≫ (zeroIdeal Y L₁ L₂ s).subschemeι)
    (hK : Dᵢ.comap k = K) (N : Y.Modules)
    [hN : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property N]
    [hN' : AlgebraicGeometry.SheafOfModules.IsInvertible Y'.sheaf.obj Y'.ringCatSheaf.property
      ((Scheme.Modules.pullback g).obj N)]
    (e : Dᵢ.subscheme ≅ (branchSituation Y L₁ L₂ s N).totalSpace)
    (he : e.hom ≫ (branchSituation Y L₁ L₂ s N).totalSpaceToBase = pᵢ)
    {W : Scheme.{u}} (c : W ⟶ K.subscheme)
    (z : W ⟶ (zeroIdeal Y' ((Scheme.Modules.pullback g).obj L₁)
      ((Scheme.Modules.pullback g).obj L₂) (pullbackTensorSection g L₁ L₂ s)).subscheme)
    (hc : c ≫ (Scheme.IdealSheafData.subschemeMap K Dᵢ k
      (Scheme.IdealSheafData.le_map_iff_comap_le.2 hK.le)) ≫ e.hom =
      z ≫ zeroIdealBaseChangeMap s g ≫ (branchSituation Y L₁ L₂ s N).zeroSection)
    (hz : c ≫ bcProj g hsq pᵢ comm hK = z) :
    c ≫ (bcBranchIso g hsq pᵢ comm hK N e he).hom =
      z ≫ (branchSituation Y' ((Scheme.Modules.pullback g).obj L₁)
        ((Scheme.Modules.pullback g).obj L₂) (pullbackTensorSection g L₁ L₂ s)
        ((Scheme.Modules.pullback g).obj N)).zeroSection :=
  have := isInvertible_branchSituation_baseChange (s := s) g N
  comp_isoIsPullback_trans_symm_hom
    (isPullback_comp_isIso (isPullback_bcProj g hsq pᵢ comm hK) e he)
    ((branchSituation Y L₁ L₂ s N).isPullback_baseChange (zeroIdealBaseChangeMap s g)) _ _
    (((branchSituation Y L₁ L₂ s N).baseChange
      (zeroIdealBaseChangeMap s g)).zeroSection_comp_totalSpaceIsoOfIso_hom _ _)
    ((branchSituation Y L₁ L₂ s N).baseChange
      (zeroIdealBaseChangeMap s g)).zeroSection_comp_totalSpaceToBase
    ((branchSituation Y L₁ L₂ s N).zeroSection_comp_baseChangeToTotalSpace
      (zeroIdealBaseChangeMap s g))
    c z hc hz

/-- The inverse images of `Dᵢ ≤ J` give a commuting square with the projections to `D` and `D'`. -/
private theorem subschemeMap_inclusion_comp_bcProj (hsq : IsPullback k p' q g)
    (pᵢ : Dᵢ.subscheme ⟶ (zeroIdeal Y L₁ L₂ s).subscheme)
    (comm : Dᵢ.subschemeι ≫ q = pᵢ ≫ (zeroIdeal Y L₁ L₂ s).subschemeι)
    (hK : Dᵢ.comap k = K) {J : T.IdealSheafData} {J' : T'.IdealSheafData} (hJ : J.comap k = J')
    (hIJ : Dᵢ ≤ J) (hIJ' : K ≤ J') :
    Scheme.IdealSheafData.subschemeMap J' J k
          (Scheme.IdealSheafData.le_map_iff_comap_le.2 hJ.le) ≫
        (Scheme.IdealSheafData.inclusion hIJ ≫ pᵢ) =
      (Scheme.IdealSheafData.inclusion hIJ' ≫ bcProj g hsq pᵢ comm hK) ≫
        zeroIdealBaseChangeMap s g := by
  rw [Category.assoc, bcProj_comp_zeroIdealBaseChangeMap g hsq pᵢ comm hK,
    ← Category.assoc, ← Category.assoc, subschemeMap_inclusion_comm k hK hJ hIJ hIJ']

/-- If the inclusion `Dᵢ ≤ J` is the zero section after the identification `e` of a branch, the
same holds for the inverse images of `Dᵢ` and `J` and the identification of `bcBranchIso`. -/
private theorem inclusion_comp_bcBranchIso_hom (hsq : IsPullback k p' q g)
    (pᵢ : Dᵢ.subscheme ⟶ (zeroIdeal Y L₁ L₂ s).subscheme)
    (comm : Dᵢ.subschemeι ≫ q = pᵢ ≫ (zeroIdeal Y L₁ L₂ s).subschemeι)
    (hK : Dᵢ.comap k = K) (N : Y.Modules)
    [hN : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property N]
    [hN' : AlgebraicGeometry.SheafOfModules.IsInvertible Y'.sheaf.obj Y'.ringCatSheaf.property
      ((Scheme.Modules.pullback g).obj N)]
    (e : Dᵢ.subscheme ≅ (branchSituation Y L₁ L₂ s N).totalSpace)
    (he : e.hom ≫ (branchSituation Y L₁ L₂ s N).totalSpaceToBase = pᵢ)
    {J : T.IdealSheafData} {J' : T'.IdealSheafData} (hJ : J.comap k = J') (hIJ : Dᵢ ≤ J)
    (hIJ' : K ≤ J')
    (hzs : Scheme.IdealSheafData.inclusion hIJ ≫ e.hom =
      (Scheme.IdealSheafData.inclusion hIJ ≫ pᵢ) ≫ (branchSituation Y L₁ L₂ s N).zeroSection) :
    Scheme.IdealSheafData.inclusion hIJ' ≫ (bcBranchIso g hsq pᵢ comm hK N e he).hom =
      (Scheme.IdealSheafData.inclusion hIJ' ≫ bcProj g hsq pᵢ comm hK) ≫
        (branchSituation Y' ((Scheme.Modules.pullback g).obj L₁)
          ((Scheme.Modules.pullback g).obj L₂) (pullbackTensorSection g L₁ L₂ s)
          ((Scheme.Modules.pullback g).obj N)).zeroSection := by
  refine comp_bcBranchIso_hom g hsq pᵢ comm hK N e he _ _ ?_ rfl
  rw [← Category.assoc, subschemeMap_inclusion_comm k hK hJ hIJ hIJ', Category.assoc, hzs]
  exact (Category.assoc _ _ _).symm.trans
    ((subschemeMap_inclusion_comp_bcProj g hsq pᵢ comm hK hJ hIJ hIJ' =≫ _).trans
      (Category.assoc _ _ _))

end BranchTransport

/-! ### The base-changed diagram -/

section Transport

variable {Y Y' : Scheme.{u}} {L₁ L₂ : Y.Modules}
  [h₁ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₁]
  [h₂ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₂]
  {s : Γ(Stacks.Divisors.tensorModules L₁ L₂, ⊤)} (g : Y' ⟶ Y)
  [i₁ : AlgebraicGeometry.SheafOfModules.IsInvertible Y'.sheaf.obj Y'.ringCatSheaf.property
    ((Scheme.Modules.pullback g).obj L₁)]
  [i₂ : AlgebraicGeometry.SheafOfModules.IsInvertible Y'.sheaf.obj Y'.ringCatSheaf.property
    ((Scheme.Modules.pullback g).obj L₂)]

omit i₂ in
include h₁ h₂ in
/-- **Tag 0F97(3) for the base-changed diagram, first branch**: the inverse image of `D₁` is the
zero scheme of the transported section `s₁'`. -/
theorem Decomposition.comap_D₁_baseChange (R : Decomposition Y L₁ L₂ s) {T' : Scheme.{u}}
    {k : T' ⟶ R.total} {p' : T' ⟶ Y'} (hsq : IsPullback k p' R.p g) :
    R.D₁.comap k = (Stacks.Divisors.zeroScheme T'
      ((Scheme.Modules.pullback p').obj ((Scheme.Modules.pullback g).obj L₁))
      (baseChangeSection hsq.w L₁ R.s₁)) :=
  (congrArg (fun K : R.total.IdealSheafData => K.comap k) R.zeroScheme₁).trans
    (comap_zeroScheme_baseChange hsq.w L₁ R.s₁)

omit i₁ in
include h₁ h₂ in
/-- **Tag 0F97(3) for the base-changed diagram, second branch.** -/
theorem Decomposition.comap_D₂_baseChange (R : Decomposition Y L₁ L₂ s) {T' : Scheme.{u}}
    {k : T' ⟶ R.total} {p' : T' ⟶ Y'} (hsq : IsPullback k p' R.p g) :
    R.D₂.comap k = (Stacks.Divisors.zeroScheme T'
      ((Scheme.Modules.pullback p').obj ((Scheme.Modules.pullback g).obj L₂))
      (baseChangeSection hsq.w L₂ R.s₂)) :=
  (congrArg (fun K : R.total.IdealSheafData => K.comap k) R.zeroScheme₂).trans
    (comap_zeroScheme_baseChange hsq.w L₂ R.s₂)

variable (R : Decomposition Y L₁ L₂ s) {T' : Scheme.{u}} {k : T' ⟶ R.total} {p' : T' ⟶ Y'}
  (hsq : IsPullback k p' R.p g) {K₁ K₂ : T'.IdealSheafData} (hK₁ : R.D₁.comap k = K₁)
  (hK₂ : R.D₂.comap k = K₂)

include h₁ h₂ hK₁ hK₂ in
/-- The inverse image of the scheme-theoretic intersection `D₁ ∩ D₂` is the intersection of the
two inverse images: the inverse image of ideal sheaves preserves joins. -/
theorem Decomposition.comap_sup_baseChange : (R.D₁ ⊔ R.D₂).comap k = K₁ ⊔ K₂ :=
  (Scheme.IdealSheafData.comap_sup _ _ _).trans (by rw [hK₁, hK₂])

include h₁ h₂ in
/-- The two squares over `D₁ ∩ D₂` and over `D₁` of the base change agree. -/
theorem Decomposition.subschemeMap_inclusion_comp_proj₁
    (hKJ : (R.D₁ ⊔ R.D₂).comap k = K₁ ⊔ K₂) :
    Scheme.IdealSheafData.subschemeMap (K₁ ⊔ K₂) (R.D₁ ⊔ R.D₂) k
          (Scheme.IdealSheafData.le_map_iff_comap_le.2 hKJ.le) ≫
        (Scheme.IdealSheafData.inclusion (le_sup_left : R.D₁ ≤ R.D₁ ⊔ R.D₂) ≫ R.p₁) =
      (Scheme.IdealSheafData.inclusion (le_sup_left : K₁ ≤ K₁ ⊔ K₂) ≫
        bcProj g hsq R.p₁ R.comm₁ hK₁) ≫ zeroIdealBaseChangeMap s g :=
  subschemeMap_inclusion_comp_bcProj g hsq R.p₁ R.comm₁ hK₁ hKJ le_sup_left le_sup_left

include h₁ h₂ in
/-- The two squares over `D₁ ∩ D₂` and over `D₂` of the base change agree. -/
theorem Decomposition.subschemeMap_inclusion_comp_proj₂
    (hKJ : (R.D₁ ⊔ R.D₂).comap k = K₁ ⊔ K₂) :
    Scheme.IdealSheafData.subschemeMap (K₁ ⊔ K₂) (R.D₁ ⊔ R.D₂) k
          (Scheme.IdealSheafData.le_map_iff_comap_le.2 hKJ.le) ≫
        (Scheme.IdealSheafData.inclusion (le_sup_right : R.D₂ ≤ R.D₁ ⊔ R.D₂) ≫ R.p₂) =
      (Scheme.IdealSheafData.inclusion (le_sup_right : K₂ ≤ K₁ ⊔ K₂) ≫
        bcProj g hsq R.p₂ R.comm₂ hK₂) ≫ zeroIdealBaseChangeMap s g :=
  subschemeMap_inclusion_comp_bcProj g hsq R.p₂ R.comm₂ hK₂ hKJ le_sup_right le_sup_right

include h₁ h₂ in
/-- **Tag 0F97(6) for the base-changed diagram**: the scheme-theoretic intersection of the two
inverse images maps isomorphically to `D'`. The intersection is the fibre product of `D₁ ∩ D₂`
with `D'` over `D`, and an isomorphism stays one under base change. -/
theorem Decomposition.bcIntersection_isIso
    (hKJ : (R.D₁ ⊔ R.D₂).comap k = K₁ ⊔ K₂) :
    IsIso (Scheme.IdealSheafData.inclusion (le_sup_left : K₁ ≤ K₁ ⊔ K₂) ≫
      bcProj g hsq R.p₁ R.comm₁ hK₁) :=
  MorphismProperty.of_isPullback
    (isPullback_over_zeroIdealBaseChangeMap g hsq hKJ
      (Scheme.IdealSheafData.inclusion (le_sup_left : R.D₁ ≤ R.D₁ ⊔ R.D₂) ≫ R.p₁)
      (Scheme.IdealSheafData.inclusion (le_sup_left : K₁ ≤ K₁ ⊔ K₂) ≫
        bcProj g hsq R.p₁ R.comm₁ hK₁)
      (by
        rw [Category.assoc, ← R.comm₁, ← Category.assoc,
          Scheme.IdealSheafData.inclusion_subschemeι])
      (by
        rw [Category.assoc, ← bcProj_comp_subschemeι g hsq R.p₁ R.comm₁ hK₁, ← Category.assoc,
          Scheme.IdealSheafData.inclusion_subschemeι])
      (R.subschemeMap_inclusion_comp_proj₁ g hsq hK₁ hKJ))
    R.intersection_isIso

include h₁ h₂ in
/-- **Tag 0F97(7) for the base-changed diagram, first branch**: the intersection of the two
inverse images maps to the first of them by the zero section of its line bundle over `D'`. -/
theorem Decomposition.bcIntersection_zeroSection₁
    (hKJ : (R.D₁ ⊔ R.D₂).comap k = K₁ ⊔ K₂) :
    Scheme.IdealSheafData.inclusion (le_sup_left : K₁ ≤ K₁ ⊔ K₂) ≫
        (bcBranchIso g hsq R.p₁ R.comm₁ hK₁ L₂ R.branch₁ R.branch₁_toBase).hom =
      (Scheme.IdealSheafData.inclusion (le_sup_left : K₁ ≤ K₁ ⊔ K₂) ≫
        bcProj g hsq R.p₁ R.comm₁ hK₁) ≫ (branchSituation Y' ((Scheme.Modules.pullback g).obj L₁)
      ((Scheme.Modules.pullback g).obj L₂) (pullbackTensorSection g L₁ L₂ s)
      ((Scheme.Modules.pullback g).obj L₂)).zeroSection := by
  exact inclusion_comp_bcBranchIso_hom g hsq R.p₁ R.comm₁ hK₁ _ R.branch₁
    R.branch₁_toBase hKJ le_sup_left le_sup_left R.intersection_zeroSection₁

include h₁ h₂ in
/-- **Tag 0F97(7) for the base-changed diagram, second branch.** -/
theorem Decomposition.bcIntersection_zeroSection₂
    (hKJ : (R.D₁ ⊔ R.D₂).comap k = K₁ ⊔ K₂) :
    Scheme.IdealSheafData.inclusion (le_sup_right : K₂ ≤ K₁ ⊔ K₂) ≫
        (bcBranchIso g hsq R.p₂ R.comm₂ hK₂ L₁ R.branch₂ R.branch₂_toBase).hom =
      (Scheme.IdealSheafData.inclusion (le_sup_right : K₂ ≤ K₁ ⊔ K₂) ≫
        bcProj g hsq R.p₂ R.comm₂ hK₂) ≫ (branchSituation Y' ((Scheme.Modules.pullback g).obj L₁)
      ((Scheme.Modules.pullback g).obj L₂) (pullbackTensorSection g L₁ L₂ s)
      ((Scheme.Modules.pullback g).obj L₁)).zeroSection := by
  exact inclusion_comp_bcBranchIso_hom g hsq R.p₂ R.comm₂ hK₂ _ R.branch₂
    R.branch₂_toBase hKJ le_sup_right le_sup_right R.intersection_zeroSection₂

include h₁ h₂ in
/-- **Tag 0F97(5) for the base-changed diagram**: the inverse image of `D'` under `p'` is the
scheme-theoretic union of the two base-changed branches. This is derived from conditions (1),
(3), (4), (6) and (7) for the base-changed diagram and uses condition (5) for `R` nowhere: the
inverse image is the zero scheme of `s₁' ⊗ s₂'` by condition (1), and the zero scheme of a
product of two sections of invertible modules is the union of the two zero schemes once the
second restricts to a regular section of the first — which conditions (3), (4), (6) and (7)
supply through `Stacks.LineBundle.isRegularSection_restrict_of_inf_eq_zeroSection`. -/
theorem Decomposition.bcPreimage_eq_union (R : Decomposition Y L₁ L₂ s) {T' : Scheme.{u}}
    {k : T' ⟶ R.total} {p' : T' ⟶ Y'} (hsq : IsPullback k p' R.p g) :
    (zeroIdeal Y' ((Scheme.Modules.pullback g).obj L₁) ((Scheme.Modules.pullback g).obj L₂)
        (pullbackTensorSection g L₁ L₂ s)).comap p' =
      (Stacks.Divisors.zeroScheme T'
          ((Scheme.Modules.pullback p').obj ((Scheme.Modules.pullback g).obj L₁))
          (baseChangeSection hsq.w L₁ R.s₁)) ⊓
        (Stacks.Divisors.zeroScheme T'
          ((Scheme.Modules.pullback p').obj ((Scheme.Modules.pullback g).obj L₂))
          (baseChangeSection hsq.w L₂ R.s₂)) := by
  have hprod : pullbackTensorSection p' ((Scheme.Modules.pullback g).obj L₁)
        ((Scheme.Modules.pullback g).obj L₂) (pullbackTensorSection g L₁ L₂ s) =
      Stacks.Divisors.tensorSection
        ((Scheme.Modules.pullback p').obj ((Scheme.Modules.pullback g).obj L₁))
        ((Scheme.Modules.pullback p').obj ((Scheme.Modules.pullback g).obj L₂)) ⊤
        (baseChangeSection hsq.w L₁ R.s₁) (baseChangeSection hsq.w L₂ R.s₂) :=
    Stacks.PullbackTensorIso.pullbackTensorSection_of_square hsq.w L₁ L₂ s R.s₁ R.s₂
      R.pullback_section_eq
  have hreg := Stacks.LineBundle.isRegularSection_restrict_of_inf_eq_zeroSection
    (Stacks.Divisors.zeroScheme T'
      ((Scheme.Modules.pullback p').obj ((Scheme.Modules.pullback g).obj L₁))
      (baseChangeSection hsq.w L₁ R.s₁))
    (Stacks.Divisors.zeroScheme T'
      ((Scheme.Modules.pullback p').obj ((Scheme.Modules.pullback g).obj L₂))
      (baseChangeSection hsq.w L₂ R.s₂))
    ((Scheme.Modules.pullback p').obj ((Scheme.Modules.pullback g).obj L₂))
    (baseChangeSection hsq.w L₂ R.s₂) rfl
    (branchSituation Y' ((Scheme.Modules.pullback g).obj L₁)
      ((Scheme.Modules.pullback g).obj L₂) (pullbackTensorSection g L₁ L₂ s)
      ((Scheme.Modules.pullback g).obj L₂))
    (bcBranchIso g hsq R.p₁ R.comm₁ (R.comap_D₁_baseChange g hsq) L₂ R.branch₁ R.branch₁_toBase)
    (Scheme.IdealSheafData.inclusion (le_sup_left) ≫
      bcProj g hsq R.p₁ R.comm₁ (R.comap_D₁_baseChange g hsq))
    (R.bcIntersection_isIso g hsq (R.comap_D₁_baseChange g hsq)
      (R.comap_sup_baseChange (R.comap_D₁_baseChange g hsq) (R.comap_D₂_baseChange g hsq)))
    (R.bcIntersection_zeroSection₁ g hsq (R.comap_D₁_baseChange g hsq)
      (R.comap_sup_baseChange (R.comap_D₁_baseChange g hsq) (R.comap_D₂_baseChange g hsq)))
  refine (comap_zeroIdeal_of_tensorSection_eq (pullbackTensorSection g L₁ L₂ s) p'
    (baseChangeSection hsq.w L₁ R.s₁) (baseChangeSection hsq.w L₂ R.s₂) hprod).trans ?_
  exact (Stacks.Divisors.zeroScheme_tensorSection_eq_inf _ _ _ _ hreg).symm

include h₁ h₂ in
/-- **The base change of a diagram as in [Stacks, Tag 0F97]**, for an arbitrary cartesian square
over `p` and `g`: the total space is the fibre product, the two closed subschemes are the
inverse images of `D₁` and `D₂` — presented as the zero schemes of the transported sections —
and the two sections are the transports of `s₁` and `s₂`. All seven conditions of the tag hold
for it. -/
def Decomposition.baseChange (R : Decomposition Y L₁ L₂ s) {T' : Scheme.{u}}
    {k : T' ⟶ R.total} {p' : T' ⟶ Y'} (hsq : IsPullback k p' R.p g) :
    Decomposition Y' ((Scheme.Modules.pullback g).obj L₁) ((Scheme.Modules.pullback g).obj L₂)
      (pullbackTensorSection g L₁ L₂ s) where
  total := T'
  p := p'
  D₁ := (Stacks.Divisors.zeroScheme T'
      ((Scheme.Modules.pullback p').obj ((Scheme.Modules.pullback g).obj L₁))
      (baseChangeSection hsq.w L₁ R.s₁))
  D₂ := (Stacks.Divisors.zeroScheme T'
      ((Scheme.Modules.pullback p').obj ((Scheme.Modules.pullback g).obj L₂))
      (baseChangeSection hsq.w L₂ R.s₂))
  p₁ := bcProj g hsq R.p₁ R.comm₁ (R.comap_D₁_baseChange g hsq)
  p₂ := bcProj g hsq R.p₂ R.comm₂ (R.comap_D₂_baseChange g hsq)
  comm₁ := bcProj_comp_subschemeι g hsq R.p₁ R.comm₁ (R.comap_D₁_baseChange g hsq)
  comm₂ := bcProj_comp_subschemeι g hsq R.p₂ R.comm₂ (R.comap_D₂_baseChange g hsq)
  s₁ := baseChangeSection hsq.w L₁ R.s₁
  s₂ := baseChangeSection hsq.w L₂ R.s₂
  pullback_section_eq :=
    Stacks.PullbackTensorIso.pullbackTensorSection_of_square hsq.w L₁ L₂ s R.s₁ R.s₂
      R.pullback_section_eq
  p_locallyOfFiniteType := MorphismProperty.of_isPullback hsq R.p_locallyOfFiniteType
  p_quasiCompact := MorphismProperty.of_isPullback hsq R.p_quasiCompact
  p_flat := MorphismProperty.of_isPullback hsq R.p_flat
  p_relativeDimension :=
    letI : LocallyOfFiniteType R.p := R.p_locallyOfFiniteType
    AlgebraicGeometry.RelativeDimension.of_isPullback hsq R.p_relativeDimension
  zeroScheme₁ := rfl
  zeroScheme₂ := rfl
  branch₁ :=
    bcBranchIso g hsq R.p₁ R.comm₁ (R.comap_D₁_baseChange g hsq) L₂ R.branch₁ R.branch₁_toBase
  branch₁_toBase :=
    bcBranchIso_hom_comp_totalSpaceToBase g hsq R.p₁ R.comm₁ (R.comap_D₁_baseChange g hsq) L₂
      R.branch₁ R.branch₁_toBase
  branch₂ :=
    bcBranchIso g hsq R.p₂ R.comm₂ (R.comap_D₂_baseChange g hsq) L₁ R.branch₂ R.branch₂_toBase
  branch₂_toBase :=
    bcBranchIso_hom_comp_totalSpaceToBase g hsq R.p₂ R.comm₂ (R.comap_D₂_baseChange g hsq) L₁
      R.branch₂ R.branch₂_toBase
  preimage_eq_union := R.bcPreimage_eq_union g hsq
  intersection_isIso := R.bcIntersection_isIso g hsq (R.comap_D₁_baseChange g hsq)
    (R.comap_sup_baseChange (R.comap_D₁_baseChange g hsq) (R.comap_D₂_baseChange g hsq))
  intersection_zeroSection₁ := R.bcIntersection_zeroSection₁ g hsq (R.comap_D₁_baseChange g hsq)
    (R.comap_sup_baseChange (R.comap_D₁_baseChange g hsq) (R.comap_D₂_baseChange g hsq))
  intersection_zeroSection₂ := R.bcIntersection_zeroSection₂ g hsq (R.comap_D₂_baseChange g hsq)
    (R.comap_sup_baseChange (R.comap_D₁_baseChange g hsq) (R.comap_D₂_baseChange g hsq))

end Transport

/-! ### The base-change clause of the tag -/

section Clause

variable {Y : Scheme.{u}} {L₁ L₂ : Y.Modules}
  [h₁ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₁]
  [h₂ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₂]
  {s : Γ(Stacks.Divisors.tensorModules L₁ L₂, ⊤)}

include h₁ h₂ in
/-- **[Stacks, Tag 0F97], the base-change clause**: *"Moreover, the formation of this diagram and
the sections `sᵢ` commutes with arbitrary base change."*

For every diagram as in the tag and **every** morphism of schemes `g : Y' ⟶ Y` — with no
flatness, finiteness or affineness hypothesis — the transported data is a diagram as in the tag
for the base-changed section: its total space is the fibre product `L ×_Y Y'`, its two closed
subschemes are the inverse images of `D₁` and `D₂` and its two sections are the pullbacks of `s₁`
and `s₂` read through the comparison of [Stacks, Tag 01CD].

Proved for an arbitrary diagram, so in particular for the one
`Stacks.Chow.TensorZeroScheme.decompositionOfClauses` assembles out of the construction. -/
theorem Decomposition.isStableUnderBaseChange (R : Decomposition Y L₁ L₂ s) :
    R.IsStableUnderBaseChange := by
  intro Y' g
  let : AlgebraicGeometry.SheafOfModules.IsInvertible Y'.sheaf.obj Y'.ringCatSheaf.property
      ((Scheme.Modules.pullback g).obj L₁) := Stacks.Divisors.pullback_isInvertible g L₁
  let : AlgebraicGeometry.SheafOfModules.IsInvertible Y'.sheaf.obj Y'.ringCatSheaf.property
      ((Scheme.Modules.pullback g).obj L₂) := Stacks.Divisors.pullback_isInvertible g L₂
  exact ⟨R.baseChange g (IsPullback.of_hasPullback R.p g), Limits.pullback.fst R.p g,
    Limits.pullback.condition, IsPullback.of_hasPullback R.p g,
    (R.comap_D₁_baseChange g (IsPullback.of_hasPullback R.p g)).symm,
    (R.comap_D₂_baseChange g (IsPullback.of_hasPullback R.p g)).symm, rfl, rfl⟩

end Clause

end Stacks.Chow.TensorZeroScheme

end
