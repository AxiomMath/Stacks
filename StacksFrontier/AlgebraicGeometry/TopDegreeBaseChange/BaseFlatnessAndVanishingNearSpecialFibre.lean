module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.IsoTransport
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.PointwiseOpenLocus
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DirectImageStructureSheafFlat
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.FlatNeighbourhoodOfSpecialFibre

/-!
# Vanishing near a whole special fibre, and flatness of the base from an isomorphism

Let `X --f--> Y --q--> S` be a commutative triangle of schemes and let `s` be a point of `S`.
Two steps of the argument of [Stacks, Tag 0E7L] are isolated here.

* **Vanishing on a neighbourhood of the whole special fibre.** If `R¹f_{s,*}𝒪_{X_s} = 0` then
  there is a *single* open `V` of `Y` containing every point of `Y` over `s` with
  `R¹f_*𝒪_X|_V = 0`, and the vanishing persists after an arbitrary base change `Y' ⟶ V`. This
  is conclusion (d) of [Stacks, Tag 0E7L], and conclusion (c) of [Stacks, Tag 0E7J].
  [Stacks, Tag 0E7G], which `ContractingRationalCurves.lean` carries, produces such an open
  around *one* point of `Y`; what is added here is that the complement of the support of
  `R¹f_*𝒪_X` serves for the whole fibre at once, which is what both tags assert.

* **Flatness of the base from the structure-sheaf isomorphism.** If `𝒪_Y ⟶ f_*𝒪_X` is an
  isomorphism and `f_*𝒪_X` is flat over `S`, then `q : Y ⟶ S` is flat. Together with clause (a)
  of [Stacks, Tag 0E7K], `isFlatOver_directImageStructureSheaf`, this is the source's step
  "*then we conclude that `Y` is flat over `S` by Lemma 0E7K*", which is how conclusion (a) of
  [Stacks, Tag 0E7L] is obtained from its conclusion (e).

## Main results

All in the namespace `Stacks.AlgebraicGeometry.TopDegreeBaseChange`.

* `notMem_supp_firstDirectImage_of_isZero_specialFibre`: no point of `Y` over `s` lies in the
  support of `R¹f_*𝒪_X`.
* `exists_isOpen_isZero_restrict_firstDirectImage_of_isZero_specialFibre`: the open
  neighbourhood of the whole special fibre on which `R¹f_*𝒪_X` vanishes.
* `exists_isOpen_isZero_restrict_firstDirectImage_baseChange_of_isZero_specialFibre`: the same
  open, with the vanishing after an arbitrary base change `Y' ⟶ V` as well.
* `exists_isOpen_flat_fibreDimension_le_one_and_isZero_firstDirectImage`: conclusions (b), (c)
  and (d) of [Stacks, Tag 0E7L] on a *single* open, got by intersecting that open with the one
  of `FlatNeighbourhoodOfSpecialFibre.lean`.
* `flat_of_isIso_unitToPushforwardUnit_of_isFlatOver`: the base is flat once `𝒪_Y ⟶ f_*𝒪_X` is
  invertible and `f_*𝒪_X` is flat over the base.
* `flat_of_isIso_unitToPushforwardUnit`: the same with the flatness of `f_*𝒪_X` supplied by
  clause (a) of [Stacks, Tag 0E7K].

## Why no `@[stacks 0E7L]` attribute is attached

**No `@[stacks 0E7L]` attribute is attached to anything in this file**, and no
`@[stacks 0E7J]` one either. The reasons differ for the three results.

The two vanishing statements carry the finite-type clause of [Stacks, Tag 0EX4] for
`R¹f_*𝒪_X` as `hft`, and the clause of [Stacks, Tag 0EX3] (b) — that formation of `R¹f_*𝒪_X`
commutes with base change — either at the single morphism `Y_s ⟶ Y` as `hcmp`, or quantified
over every base change as `hbc`. Neither is available in this development at fibre dimension
one; both are carried throughout this directory, by [Stacks, Tags 0E7F], [0E7G] and [0E7I]. In
the quantified form the clause *is* the base-change persistence that conclusion (d) of
[Stacks, Tag 0E7L] asserts, so a declaration carrying `hbc` cannot carry the tag; for the same
reason `FlatNeighbourhoodOfSpecialFibre.lean` withholds the attribute for clause (c) of
[Stacks, Tag 0E7J]. The single instance `hcmp` gives away no part of the tag's conclusion, but it
is still a hypothesis the source does not make, so no attribute is attached to that statement
either.

The flatness statement assumes that `𝒪_Y ⟶ f_*𝒪_X` is an isomorphism, which is conclusion (e)
of [Stacks, Tag 0E7L]; a declaration assuming one conclusion of a tag cannot carry it.

What is still missing for [Stacks, Tag 0E7L] itself is conclusion (e): that `𝒪_V ⟶ f_*𝒪_X|_V`
is an isomorphism. Its surjectivity is clause (d) of [Stacks, Tag 0E7J], whose proof in the
source runs through a closed immersion of `Y` into the spectrum of a polynomial ring on a set of
variables, a limit presentation of the base over its finite type `ℤ`-subalgebras, and
pseudo-coherence of `RΓ(X, 𝒪_X)`; none of that is in this development. Injectivity is then
[Stacks, Tag 00ME],
`Module.Flat.injective_and_flat_quotient_range_of_injective_mapQ_maximalIdeal_of_isNoetherianRing`,
applied to the stalk `𝒪_{Y,y}` mapping to `(f_*𝒪_X)_y`, which is `𝒪_{S,s}`-flat by clause (a)
of [Stacks, Tag 0E7K]; that tag needs `𝒪_{Y,y}` Noetherian, which under the hypotheses of
[Stacks, Tag 0E7L] is again a consequence of the limit presentation and of the hypothesis that
`Y ⟶ S` is locally of finite presentation. Finally the persistence of (e) under base change is
clause (b) of [Stacks, Tag 0E7K], recorded as open in `DirectImageStructureSheafFlat.lean`.

## Implementation notes

The induced morphism on the fibres over `s` is written `pullback.snd f (q.fiberι s)`: its
target is `Y_s = q.fiber s`, and its source `X ×_Y Y_s` is `X_s`, the fibre of `X ⟶ S` over `s`.
This is the spelling in which the base-change hypothesis `hbc` is already stated, so no transport
is needed; the `Stacks.Flatness.fiberHom f q s` of `StacksFrontier/AlgebraicGeometry/Morphisms/Flat/FibrewiseFiber.lean` is the same morphism
presented as a lift into a fibre product.

The open is the complement of `SheafOfModules.supp (R¹f_*𝒪_X)`, which is closed because of the
finite-type clause `hft` (`SheafOfModules.isClosed_supp`, [Stacks, Tag 056J]). Every point of `Y`
over `s` is in the image of `q.fiberι s` (`AlgebraicGeometry.Scheme.Hom.range_fiberι`), so the
vanishing of the pullback of `R¹f_*𝒪_X` to `Y_s` puts all of them outside that support.

## References

* [Stacks Project, Tag 0E7L](https://stacks.math.columbia.edu/tag/0E7L)
* [Stacks Project, Tag 0E7J](https://stacks.math.columbia.edu/tag/0E7J)
* [Stacks Project, Tag 0E7K](https://stacks.math.columbia.edu/tag/0E7K)
* [Stacks Project, Tag 0E7G](https://stacks.math.columbia.edu/tag/0E7G)
* [Stacks Project, Tag 056J](https://stacks.math.columbia.edu/tag/056J)
* [Stacks Project, Tag 00ME](https://stacks.math.columbia.edu/tag/00ME)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance] HasDerivedCategory.standard

noncomputable section

variable {X Y S : Scheme.{u}}

/-! ### Vanishing of `R¹f_*𝒪_X` on a neighbourhood of the whole special fibre -/

/-- **A module vanishes on an open disjoint from its support.** Restriction commutes with taking
stalks (`AlgebraicGeometry.Scheme.Modules.restrictStalkNatIso`), and a module all of whose
stalks are zero objects is a zero object. -/
theorem isZero_restrict_of_forall_notMem_supp (M : Y.Modules) (V : Y.Opens)
    (h : ∀ y : Y, y ∈ V → y ∉ SheafOfModules.supp M) :
    IsZero ((Scheme.Modules.restrictFunctor V.ι).obj M) := by
  refine isZero_of_forall_isZero_stalk _ fun w => ?_
  exact IsZero.of_iso ((notMem_supp_iff_isZero_stalk _ _).mp (h _ w.2))
    ((Scheme.Modules.restrictStalkNatIso _ w).app M)

/-- **The base-change half of a vanishing over an open.** If `R¹f_*𝒪_X` vanishes over `V`, then
`R¹f'_*𝒪_{X'} = 0` for the base change of `f` along every `g : Y' ⟶ V`.

The restriction of a module to an open is its pullback along the inclusion
(`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`), so the vanishing over `V` is
the vanishing of the pullback along `V.ι`; pulling that back further along `g` and using the
compatibility of pullback with composition gives the vanishing of the pullback along `g ≫ V.ι`,
which the base-change clause `hbc` identifies with `R¹f'_*𝒪_{X'}`. -/
theorem isZero_firstDirectImage_baseChange_of_isZero_restrict (f : X ⟶ Y)
    (hbc : FirstDirectImageCommutesBaseChange f) (V : Y.Opens)
    (hres : IsZero ((Scheme.Modules.restrictFunctor V.ι).obj
      (firstDirectImageStructureSheaf f)))
    {Y' : Scheme.{u}} (g : Y' ⟶ V.toScheme) :
    IsZero (firstDirectImageStructureSheaf (pullback.snd f (g ≫ V.ι))) := by
  have h1 : IsZero ((Scheme.Modules.pullback V.ι).obj (firstDirectImageStructureSheaf f)) :=
    IsZero.of_iso hres
      ((Scheme.Modules.restrictFunctorIsoPullback V.ι).app
        (firstDirectImageStructureSheaf f)).symm
  have h2 : IsZero ((Scheme.Modules.pullback (g ≫ V.ι)).obj
      (firstDirectImageStructureSheaf f)) :=
    IsZero.of_iso (Functor.map_isZero (Scheme.Modules.pullback g) h1)
      ((Scheme.Modules.pullbackComp g V.ι).app (firstDirectImageStructureSheaf f)).symm
  exact IsZero.of_iso h2 (hbc (g ≫ V.ι)).symm

/-- **No point of `Y` over `s` meets the support of `R¹f_*𝒪_X`.** The comparison `hcmp` is the
single instance of the clause of [Stacks, Tag 0EX3] (b) at the morphism `Y_s ⟶ Y`: it says the
pullback of `R¹f_*𝒪_X` to `Y_s` is `R¹f_{s,*}𝒪_{X_s}`, which the hypothesis makes zero. Every
point of `Y` over `s` is in the image of `Y_s ⟶ Y`
(`AlgebraicGeometry.Scheme.Hom.range_fiberι`), so [Stacks, Tag 056J] puts it outside the
support — the source's Nakayama step, which is where the finite-type clause `hft` enters. -/
theorem notMem_supp_firstDirectImage_of_isZero_specialFibre (f : X ⟶ Y) (q : Y ⟶ S) (s : S)
    (hft : (firstDirectImageStructureSheaf f).IsFiniteType)
    (hcmp : (Scheme.Modules.pullback (q.fiberι s)).obj (firstDirectImageStructureSheaf f) ≅
      firstDirectImageStructureSheaf (pullback.snd f (q.fiberι s)))
    (hfib : IsZero (firstDirectImageStructureSheaf (pullback.snd f (q.fiberι s))))
    (y : Y) (hy : q y = s) :
    y ∉ SheafOfModules.supp (firstDirectImageStructureSheaf f) := by
  have hmem : y ∈ Set.range (q.fiberι s) := by
    rw [Scheme.Hom.range_fiberι]
    exact hy
  obtain ⟨y', rfl⟩ := hmem
  exact notMem_supp_of_isZero_pullback (firstDirectImageStructureSheaf f) hft
    (q.fiberι s) y' (IsZero.of_iso hfib hcmp)

/-- **An open around the special fibre missing the support of `R¹f_*𝒪_X`**: the complement of the
support, which is closed by the finite-type clause `hft`. -/
private theorem exists_isOpen_forall_notMem_supp_firstDirectImage (f : X ⟶ Y) (q : Y ⟶ S) (s : S)
    (hft : (firstDirectImageStructureSheaf f).IsFiniteType)
    (hcmp : (Scheme.Modules.pullback (q.fiberι s)).obj (firstDirectImageStructureSheaf f) ≅
      firstDirectImageStructureSheaf (pullback.snd f (q.fiberι s)))
    (hfib : IsZero (firstDirectImageStructureSheaf (pullback.snd f (q.fiberι s)))) :
    ∃ V : Y.Opens, (∀ y : Y, q y = s → y ∈ V) ∧
      ∀ y : Y, y ∈ V → y ∉ SheafOfModules.supp (firstDirectImageStructureSheaf f) :=
  ⟨⟨(SheafOfModules.supp (firstDirectImageStructureSheaf f))ᶜ,
    (SheafOfModules.isClosed_supp (firstDirectImageStructureSheaf f)).isOpen_compl⟩,
    notMem_supp_firstDirectImage_of_isZero_specialFibre f q s hft hcmp hfib, fun _ hy => hy⟩

/-- **The first half of conclusion (d) of [Stacks, Tag 0E7L]**, which is the first half of
conclusion (c) of [Stacks, Tag 0E7J]: an open `V` of `Y` containing every point over `s` with
`R¹f_*𝒪_X|_V = 0`. Only one instance of the base-change clause of [Stacks, Tag 0EX3] (b) is
used, the comparison `hcmp` at `Y_s ⟶ Y`; nothing is assumed about base changes of `f` by
morphisms `S' ⟶ S`, which is what the second half of the conclusion is about.

The open is the complement of the support of `R¹f_*𝒪_X`, closed by the finite-type clause
`hft`; a module vanishes on an open where all its stalks do. -/
theorem exists_isOpen_isZero_restrict_firstDirectImage_of_isZero_specialFibre
    (f : X ⟶ Y) (q : Y ⟶ S) (s : S)
    (hft : (firstDirectImageStructureSheaf f).IsFiniteType)
    (hcmp : (Scheme.Modules.pullback (q.fiberι s)).obj (firstDirectImageStructureSheaf f) ≅
      firstDirectImageStructureSheaf (pullback.snd f (q.fiberι s)))
    (hfib : IsZero (firstDirectImageStructureSheaf (pullback.snd f (q.fiberι s)))) :
    ∃ V : Y.Opens, (∀ y : Y, q y = s → y ∈ V) ∧
      IsZero ((Scheme.Modules.restrictFunctor V.ι).obj (firstDirectImageStructureSheaf f)) := by
  obtain ⟨V, hV, hn⟩ := exists_isOpen_forall_notMem_supp_firstDirectImage f q s hft hcmp hfib
  exact ⟨V, hV, isZero_restrict_of_forall_notMem_supp _ _ hn⟩

/-- **Conclusion (d) of [Stacks, Tag 0E7L]**, which is conclusion (c) of [Stacks, Tag 0E7J].
Let `X --f--> Y --q--> S` be a commutative triangle and `s` a point of `S`. If
`R¹f_{s,*}𝒪_{X_s} = 0` for the induced morphism `f_s : X_s ⟶ Y_s`, then there is an open `V` of
`Y` containing every point of `Y` lying over `s` such that `R¹f_*𝒪_X|_V = 0`, and
`R¹f'_*𝒪_{X'} = 0` for the base change along every `g : Y' ⟶ V`.

The base-change clause `hbc` turns the hypothesis into the vanishing of the pullback of
`R¹f_*𝒪_X` along `Y_s ⟶ Y`, so by [Stacks, Tag 056J] no point in the image of that morphism —
that is, no point of `Y` over `s` — lies in the support of `R¹f_*𝒪_X`. The finite-type clause
`hft` makes that support closed, and its complement is the open required: a module vanishes
wherever its stalks do, and the universality after base change is `hbc` again, applied to
`g ≫ V.ι` and read through the compatibility of pullback with composition. -/
theorem exists_isOpen_isZero_restrict_firstDirectImage_baseChange_of_isZero_specialFibre
    (f : X ⟶ Y) (q : Y ⟶ S) (s : S)
    (hft : (firstDirectImageStructureSheaf f).IsFiniteType)
    (hbc : FirstDirectImageCommutesBaseChange f)
    (hfib : IsZero (firstDirectImageStructureSheaf (pullback.snd f (q.fiberι s)))) :
    ∃ V : Y.Opens, (∀ y : Y, q y = s → y ∈ V) ∧
      IsZero ((Scheme.Modules.restrictFunctor V.ι).obj (firstDirectImageStructureSheaf f)) ∧
      ∀ (Y' : Scheme.{u}) (g : Y' ⟶ V.toScheme),
        IsZero (firstDirectImageStructureSheaf (pullback.snd f (g ≫ V.ι))) := by
  obtain ⟨V, hV, hres⟩ :=
    exists_isOpen_isZero_restrict_firstDirectImage_of_isZero_specialFibre f q s hft
      (hbc (q.fiberι s)) hfib
  exact ⟨V, hV, hres, fun _ g =>
    isZero_firstDirectImage_baseChange_of_isZero_restrict f hbc V hres g⟩

/-- **Conclusions (b), (c) and (d) of [Stacks, Tag 0E7L] on a single open.** Let
`X --f--> Y --q--> S` be a commutative triangle and `s` a point of `S`. Assume `X ⟶ S` is
locally of finite presentation and flat at the points of `X_s`, that `f` is proper, that the
fibres of `f_s : X_s ⟶ Y_s` have dimension at most one and that `R¹f_{s,*}𝒪_{X_s} = 0`. Then
there is one open `Y_s ⊂ V ⊂ Y` with `f⁻¹(V)` flat over `S`, `dim(X_y) ≤ 1` for `y ∈ V` and
`R¹f_*𝒪_X|_V = 0`, the last two persisting after an arbitrary base change `Y' ⟶ V`.

The open is the intersection of the one of `exists_isOpen_flat_and_fibreDimension_le_one`, which
carries conclusions (b) and (c), with the complement of the support of `R¹f_*𝒪_X`, which carries
conclusion (d). Shrinking preserves all three: flatness because the inclusion of the smaller
open is itself flat, the dimension bound and the vanishing because they are stated pointwise and
over the open respectively.

Conclusions (a) and (e) are not here; see the module documentation for what they need. -/
theorem exists_isOpen_flat_fibreDimension_le_one_and_isZero_firstDirectImage
    (f : X ⟶ Y) (q : Y ⟶ S) (s : S)
    [LocallyOfFinitePresentation (f ≫ q)] [IsProper f]
    (hflat : ∀ x : X, (f ≫ q) x = s → IsFlatAt (f ≫ q).toLRSHom.toShHom x)
    (hdim : ∀ y : q.fiber s,
      topologicalKrullDim ((Stacks.Flatness.fiberHom f q s).fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞))
    (hft : (firstDirectImageStructureSheaf f).IsFiniteType)
    (hbc : FirstDirectImageCommutesBaseChange f)
    (hfib : IsZero (firstDirectImageStructureSheaf (pullback.snd f (q.fiberι s)))) :
    ∃ V : Y.Opens, (∀ y : Y, q y = s → y ∈ V) ∧
      Flat ((f ⁻¹ᵁ V).ι ≫ (f ≫ q)) ∧
      (∀ y : Y, y ∈ V → topologicalKrullDim (f.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞)) ∧
      IsZero ((Scheme.Modules.restrictFunctor V.ι).obj (firstDirectImageStructureSheaf f)) ∧
      (∀ (Y' : Scheme.{u}) (g : Y' ⟶ V.toScheme) (y' : Y'),
        topologicalKrullDim ((pullback.snd f (g ≫ V.ι)).fiber y') ≤ ((1 : ℕ) : WithBot ℕ∞)) ∧
      ∀ (Y' : Scheme.{u}) (g : Y' ⟶ V.toScheme),
        IsZero (firstDirectImageStructureSheaf (pullback.snd f (g ≫ V.ι))) := by
  obtain ⟨V₁, hV₁, hflat₁, hdim₁, hdimbc₁⟩ :=
    exists_isOpen_flat_and_fibreDimension_le_one f q s hflat hdim
  obtain ⟨V₂, hV₂, hn⟩ :=
    exists_isOpen_forall_notMem_supp_firstDirectImage f q s hft (hbc (q.fiberι s)) hfib
  set V : Y.Opens := V₁ ⊓ V₂ with hVdef
  have hle : V ≤ V₁ := inf_le_left
  have hres : IsZero ((Scheme.Modules.restrictFunctor V.ι).obj
      (firstDirectImageStructureSheaf f)) :=
    isZero_restrict_of_forall_notMem_supp _ V fun _ hy => hn _ hy.2
  refine ⟨V, fun y hy => ⟨hV₁ y hy, hV₂ y hy⟩, ?_, fun y hy => hdim₁ y (hle hy), hres,
    fun Y' g y' => ?_, fun _ g => isZero_firstDirectImage_baseChange_of_isZero_restrict f hbc V
      hres g⟩
  · have hpre : f ⁻¹ᵁ V ≤ f ⁻¹ᵁ V₁ := fun x hx => hle hx
    have _ : Flat ((f ⁻¹ᵁ V₁).ι ≫ (f ≫ q)) := hflat₁
    rw [← X.homOfLE_ι hpre, Category.assoc]
    infer_instance
  · have hcomp : g ≫ V.ι = (g ≫ Y.homOfLE hle) ≫ V₁.ι := by
      rw [Category.assoc, Y.homOfLE_ι]
    rw [hcomp]
    exact hdimbc₁ Y' (g ≫ Y.homOfLE hle) y'

/-! ### Flatness of the base from the structure-sheaf isomorphism -/

/-- **The base is flat once `𝒪_Y ⟶ f_*𝒪_X` is invertible and `f_*𝒪_X` is `S`-flat.** This is the
step "*then we conclude that `Y` is flat over `S` by Lemma 0E7K*" of the proof of
[Stacks, Tag 0E7L], which is how its conclusion (a) follows from its conclusion (e).

Flatness of a module over the base is a condition on stalks and depends only on the isomorphism
class of the module, so the isomorphism transports the flatness of `f_*𝒪_X` to `𝒪_Y`; flatness
of `𝒪_Y` over `S` at a point is flatness of `q` at that point. -/
theorem flat_of_isIso_unitToPushforwardUnit_of_isFlatOver (f : X ⟶ Y) (q : Y ⟶ S)
    (hiso : IsIso (Scheme.Modules.unitToPushforwardUnit f))
    (hflat : IsFlatOver q.toLRSHom.toShHom (directImageStructureSheaf f)) :
    Flat q := by
  have hunit : IsFlatOver q.toLRSHom.toShHom (SheafOfModules.unit Y.ringCatSheaf) :=
    (isFlatOver_iff_of_moduleIso q.toLRSHom.toShHom
      (@asIso _ _ _ _ (Scheme.Modules.unitToPushforwardUnit f) hiso)).mpr hflat
  rw [AlgebraicGeometry.Flat.iff_flat_stalkMap]
  exact fun y => (isFlatOverAt_unit_iff_isFlatAt q y).mp (hunit y)

/-- **[Stacks, Tag 0E7L], the passage from its conclusion (e) to its conclusion (a).** Let
`X --f--> Y --q--> S` be a commutative triangle with `X ⟶ S` flat, `f` proper,
`dim(X_y) ≤ 1` for every `y ∈ Y` and `R¹f_*𝒪_X = 0`. If `𝒪_Y ⟶ f_*𝒪_X` is an isomorphism, then
`Y` is flat over `S`.

Clause (a) of [Stacks, Tag 0E7K] makes `f_*𝒪_X` flat over `S`, and the isomorphism carries that
flatness to `𝒪_Y`. The hypothesis `hcoh` is the one that clause already carries: the residue of
[Stacks, Tag 02V7] at fibre dimension one. -/
theorem flat_of_isIso_unitToPushforwardUnit (hcoh : CohomologyVanishesAboveOne.{u})
    (f : X ⟶ Y) (q : Y ⟶ S) [Flat (f ≫ q)] [IsProper f]
    (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞))
    (hR : IsZero (firstDirectImageStructureSheaf f))
    (hiso : IsIso (Scheme.Modules.unitToPushforwardUnit f)) :
    Flat q :=
  flat_of_isIso_unitToPushforwardUnit_of_isFlatOver f q hiso
    (isFlatOver_directImageStructureSheaf hcoh f q hdim hR)

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
