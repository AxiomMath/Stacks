module

public import StacksFrontier.AlgebraicGeometry.Perfect.SingleDegreeOpen
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Sheaf
public import StacksFrontier.AlgebraicGeometry.UniformVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PushforwardClosedImmersion

/-!
# The open subscheme on which a derived module is locally free of a given rank in a given degree

Let `X` be a scheme, `E` an object of the derived category of sheaves of modules on `X`, `i` an
integer and `r` a natural number. An open `V ⊆ X` *carries `E` in degree `i` with rank `r`* when
the cohomology sheaves of `E` vanish on `V` outside degree `i` and the degree-`i` one is finite
locally free of rank `r` there; equivalently, when `E|_V` is isomorphic to a finite locally free
module of rank `r` placed in degree `i`. That condition passes to smaller opens and is local, so
the union `U` of all such opens is again one of them: it is the largest open subscheme of `X` on
which `E` is a finite locally free module of rank `r` in degree `i`.

This is the open subscheme of [stacks 0BDK] together with the first of the two descriptions the
tag gives of it, and the second description for open immersions. The tag itself, with the second
description for an arbitrary morphism of schemes and the derived pullback, is
`AlgebraicGeometry.Scheme.Modules.existsUnique_opens_singleDegreeRank_int`;
the results here are steps of its proof, registered for the parts of the tag they state.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.IsSingleDegreeRank`: the condition on an open subscheme.
* `AlgebraicGeometry.Scheme.Modules.singleDegreeRankOpen`: the open subscheme `U`, constructed as
  the union of the opens satisfying that condition.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isSingleDegreeRank_iff`: the two readings of the condition on
  an open — vanishing cohomology sheaves outside degree `i` with a locally free one in degree `i`,
  and an isomorphism of `E|_V` with a locally free module placed in degree `i` — agree.
* `AlgebraicGeometry.Scheme.Modules.isSingleDegreeRank_singleDegreeRankOpen`: the union `U`
  satisfies the condition, and
  `AlgebraicGeometry.Scheme.Modules.nonempty_iso_singleFunctor_restrict_iff_le`: an open satisfies
  it exactly when it is contained in `U`. Together these say that `U` is the open subscheme
  characterised by the condition.
* `AlgebraicGeometry.Scheme.Modules.nonempty_iso_singleFunctor_restrict_singleDegreeRankOpen` and
  `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_homology_singleDegreeRankOpen`: on
  `U` the module `E` is its own degree-`i` cohomology sheaf placed in degree `i`, and that sheaf is
  finite locally free of rank `r`.
* `AlgebraicGeometry.Scheme.Modules.factorsThrough_singleDegreeRankOpen_iff`: an open immersion
  factors through `U` exactly when `E` restricted along it is a finite locally free module of rank
  `r` placed in degree `i`.

## Implementation notes

The construction of `U` is a union of opens rather than a locus cut out by a pointwise condition,
which is what makes it an open subscheme by definition and what makes the characterisation among
opens a formality. That the union itself carries `E` in degree `i` with rank `r` is the locality
of the two constituent conditions: vanishing of a sheaf of modules is local
(`Stacks.AlgebraicGeometry.Tag01XJUniformVanishing.isZero_of_isZero_restrict`) and so is finite
local freeness of a fixed rank
(`AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_of_iSup_eq_top`); both are applied to
the cover of `U` by the preimages in `U` of the opens being united, and
`AlgebraicGeometry.Scheme.Modules.restrictPreimageIso` identifies the two-step restriction with the
one-step one.

Restriction along an open immersion is exact, so no derived functor is needed: `E` restricted along
an open immersion `f` is `CategoryTheory.Functor.mapDerivedCategory` of
`AlgebraicGeometry.Scheme.Modules.restrictFunctor f`. For the same reason restriction commutes with
the cohomology sheaves, which is what makes the two readings of the condition agree and what lets
the condition be stated on the cohomology sheaves of `E` itself rather than on those of `E|_V`.

The rank is a natural number here, where the source says "integers `i` and `r`"; for a negative
`r` no open carries `E` with that rank and the asserted open subscheme is empty.

Nothing below uses perfectness of `E`. The source needs it for the pointwise description of `U`
through the Betti numbers of the derived fibres, and for the universal property along an arbitrary
morphism; neither is proved here, and the open subscheme itself, the first description and the
universal property for open immersions hold for every object of the derived category.

## References

* [The Stacks Project, Lemma 36.31.3 (0BDK)](https://stacks.math.columbia.edu/tag/0BDK)
* [The Stacks Project, Lemma 15.77.7 (0BCD)](https://stacks.math.columbia.edu/tag/0BCD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe w v t u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.Scheme.Modules

/-! ### Restriction along isomorphisms and along nested opens -/

/-- Restricting a sheaf of modules along an isomorphism of schemes is undone by restricting along
the inverse isomorphism. -/
def restrictInvRestrictIso {Y Z : Scheme.{u}} (k : Y ⟶ Z) [IsIso k] (F : Z.Modules) :
    F ≅ (restrictFunctor (inv k)).obj ((restrictFunctor k).obj F) :=
  ((restrictFunctorId : restrictFunctor (𝟙 Z) ≅ 𝟭 Z.Modules).app F).symm ≪≫
    ((restrictFunctorCongr (IsIso.inv_hom_id k)).app F).symm ≪≫
    (restrictFunctorComp (inv k) k).app F

/-- A sheaf of modules whose restriction along an isomorphism of schemes vanishes vanishes. -/
theorem isZero_of_isZero_restrict_isIso {Y Z : Scheme.{u}} (k : Y ⟶ Z) [IsIso k] {F : Z.Modules}
    (h : IsZero ((restrictFunctor k).obj F)) : IsZero F :=
  IsZero.of_iso (Functor.map_isZero (restrictFunctor (inv k)) h) (restrictInvRestrictIso k F)

/-- Finite local freeness of rank `r`, in the sense of
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank`, depends only on the isomorphism class
of a sheaf of modules on a scheme. -/
theorem isFiniteLocallyFreeOfRankSheaf_of_iso {X : Scheme.{u}} {M N : X.Modules} {r : ℕ}
    (e : M ≅ N)
    (h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N r :=
  (isFiniteLocallyFreeOfRank_iff N r).1 (((isFiniteLocallyFreeOfRank_iff M r).2 h).of_iso e)

/-- A sheaf of modules whose restriction along an isomorphism of schemes is finite locally free of
rank `r` is itself finite locally free of rank `r`. -/
theorem isFiniteLocallyFreeOfRank_of_restrict_isIso {Y Z : Scheme.{u}} (k : Y ⟶ Z) [IsIso k]
    {F : Z.Modules} {r : ℕ} (h : IsFiniteLocallyFreeOfRank ((restrictFunctor k).obj F) r) :
    IsFiniteLocallyFreeOfRank F r :=
  (h.restrict (inv k)).of_iso (restrictInvRestrictIso k F).symm

/-- For `W ≤ V` opens of `X`, restricting a sheaf of modules to `V` and then to the preimage of `W`
in `V` is restricting it to `W`, read through the canonical isomorphism `ι_V⁻¹W ≅ W`. -/
def restrictPreimageIso {X : Scheme.{u}} {V W : X.Opens} (h : W ≤ V) (F : X.Modules) :
    (restrictFunctor (V.ι ⁻¹ᵁ W).ι).obj ((restrictFunctor V.ι).obj F) ≅
      (restrictFunctor (Scheme.Opens.isoOfLE h).hom).obj ((restrictFunctor W.ι).obj F) :=
  ((restrictFunctorComp (V.ι ⁻¹ᵁ W).ι V.ι).app F).symm ≪≫
    ((restrictFunctorCongr (Scheme.Opens.isoOfLE_hom_ι h)).app F).symm ≪≫
    (restrictFunctorComp (Scheme.Opens.isoOfLE h).hom W.ι).app F

/-- For `W ≤ V`, a sheaf of modules vanishes on `W` exactly when its restriction to `V` vanishes
on the preimage of `W`. -/
private theorem isZero_restrict_preimage_iff {X : Scheme.{u}} {V W : X.Opens} (h : W ≤ V)
    (F : X.Modules) :
    IsZero ((restrictFunctor (V.ι ⁻¹ᵁ W).ι).obj ((restrictFunctor V.ι).obj F)) ↔
      IsZero ((restrictFunctor W.ι).obj F) :=
  ⟨fun hF => isZero_of_isZero_restrict_isIso (Scheme.Opens.isoOfLE h).hom
      (IsZero.of_iso hF (restrictPreimageIso h F).symm),
    fun hF => IsZero.of_iso (Functor.map_isZero (restrictFunctor (Scheme.Opens.isoOfLE h).hom) hF)
      (restrictPreimageIso h F)⟩

/-- For `W ≤ V`, a sheaf of modules is finite locally free of rank `r` on `W` exactly when its
restriction to `V` is so on the preimage of `W`. -/
private theorem isFiniteLocallyFreeOfRank_restrict_preimage_iff {X : Scheme.{u}} {V W : X.Opens}
    (h : W ≤ V) (F : X.Modules) (r : ℕ) :
    IsFiniteLocallyFreeOfRank ((restrictFunctor (V.ι ⁻¹ᵁ W).ι).obj ((restrictFunctor V.ι).obj F))
        r ↔
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((restrictFunctor W.ι).obj F) r := by
  rw [← isFiniteLocallyFreeOfRank_iff]
  exact ⟨fun hF => isFiniteLocallyFreeOfRank_of_restrict_isIso (Scheme.Opens.isoOfLE h).hom
      (hF.of_iso (restrictPreimageIso h F)),
    fun hF => (hF.restrict (Scheme.Opens.isoOfLE h).hom).of_iso (restrictPreimageIso h F).symm⟩

/-! ### Cohomology of a module placed in a single degree -/

/-- The cohomology of an object of the derived category concentrated in degree `i` vanishes in
every other degree. -/
theorem isZero_homologyFunctor_singleFunctor_obj {C : Type t} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] (M : C) {i j : ℤ} (hj : j ≠ i) :
    IsZero ((DerivedCategory.homologyFunctor C j).obj
      ((DerivedCategory.singleFunctor C i).obj M)) := by
  rcases lt_or_gt_of_ne hj with h | h
  · exact DerivedCategory.isZero_of_isGE _ i j h
  · exact DerivedCategory.isZero_of_isLE _ i j h

/-! ### The opens on which `E` is locally free of rank `r` in degree `i` -/

variable {X : Scheme.{u}} (E : DerivedCategory X.Modules) (i : ℤ) (r : ℕ)

/-- An open `V` of `X` carries the derived module `E` in degree `i` with rank `r` when the
cohomology sheaves of `E` vanish on `V` in every degree other than `i` and the degree-`i` one is
finite locally free of rank `r` on `V`. -/
def IsSingleDegreeRank (V : X.Opens) : Prop :=
  (∀ j : ℤ, j ≠ i → IsZero ((restrictFunctor V.ι).obj
      ((DerivedCategory.homologyFunctor X.Modules j).obj E))) ∧
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((restrictFunctor V.ι).obj ((DerivedCategory.homologyFunctor X.Modules i).obj E)) r

/-- Carrying `E` in degree `i` with rank `r` passes to smaller opens. -/
theorem IsSingleDegreeRank.mono {V W : X.Opens} (hV : IsSingleDegreeRank E i r V) (h : W ≤ V) :
    IsSingleDegreeRank E i r W := by
  exact ⟨fun j hj => (isZero_restrict_preimage_iff h _).1 (Functor.map_isZero _ (hV.1 j hj)),
    (isFiniteLocallyFreeOfRank_restrict_preimage_iff h _ r).1
      (((isFiniteLocallyFreeOfRank_iff _ r).2 hV.2).restrict _)⟩

/-- On an open carrying `E` in degree `i` with rank `r`, the degree-`i` cohomology sheaf of `E|_V`
is finite locally free of rank `r`. -/
private theorem isFiniteLocallyFreeOfRank_homology_restrict {V : X.Opens}
    (hV : IsSingleDegreeRank E i r V) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((DerivedCategory.homologyFunctor V.toScheme.Modules i).obj
        ((restrictFunctor V.ι).mapDerivedCategory.obj E)) r :=
  isFiniteLocallyFreeOfRankSheaf_of_iso
    ((homologyFunctor_mapDerivedCategory_restrictFunctor_iso V.ι i).app E).symm hV.2

/-- **Carrying `E` in degree `i` with rank `r` is being a locally free module of rank `r` placed in
degree `i`.** On an open `V` of `X` the cohomology sheaves of `E` vanish outside degree `i` with a
finite locally free degree-`i` one of rank `r` exactly when `E|_V` is isomorphic to a finite
locally free module of rank `r` placed in degree `i`. -/
theorem isSingleDegreeRank_iff (V : X.Opens) :
    IsSingleDegreeRank E i r V ↔
      ∃ M : V.toScheme.Modules,
        AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r ∧
          Nonempty ((restrictFunctor V.ι).mapDerivedCategory.obj E ≅
            (DerivedCategory.singleFunctor V.toScheme.Modules i).obj M) := by
  constructor
  · intro hV
    refine ⟨(DerivedCategory.homologyFunctor V.toScheme.Modules i).obj
        ((restrictFunctor V.ι).mapDerivedCategory.obj E), ?_,
      nonempty_iso_singleFunctor_homologyFunctor_restrict V.ι E i hV.1⟩
    exact isFiniteLocallyFreeOfRank_homology_restrict E i r hV
  · rintro ⟨M, hM, ⟨e⟩⟩
    refine ⟨fun j hj => ?_, ?_⟩
    · refine IsZero.of_iso ?_
        ((homologyFunctor_mapDerivedCategory_restrictFunctor_iso V.ι j).app E).symm
      exact IsZero.of_iso (isZero_homologyFunctor_singleFunctor_obj M hj)
        ((DerivedCategory.homologyFunctor V.toScheme.Modules j).mapIso e)
    · refine isFiniteLocallyFreeOfRankSheaf_of_iso
        (((DerivedCategory.homologyFunctor V.toScheme.Modules i).mapIso e ≪≫
            (DerivedCategory.singleFunctorCompHomologyFunctorIso
              V.toScheme.Modules i).app M).symm ≪≫
          (homologyFunctor_mapDerivedCategory_restrictFunctor_iso V.ι i).app E) hM

/-- Being a locally free module of rank `r` in degree `i` transports along a factorisation: if
`h ≫ g = k` are open immersions and `E` restricted along `g` is a finite locally free module of
rank `r` placed in degree `i`, then so is `E` restricted along `k`. -/
theorem nonempty_iso_singleFunctor_restrict_of_comp {Y Z : Scheme.{u}} (g : Y ⟶ X)
    [IsOpenImmersion g] (h : Z ⟶ Y) [IsOpenImmersion h] (k : Z ⟶ X) [IsOpenImmersion k]
    (hk : h ≫ g = k)
    (hg : ∃ M : Y.Modules,
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r ∧
        Nonempty ((restrictFunctor g).mapDerivedCategory.obj E ≅
          (DerivedCategory.singleFunctor Y.Modules i).obj M)) :
    ∃ M : Z.Modules,
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r ∧
        Nonempty ((restrictFunctor k).mapDerivedCategory.obj E ≅
          (DerivedCategory.singleFunctor Z.Modules i).obj M) := by
  obtain ⟨M, hM, ⟨e⟩⟩ := hg
  refine ⟨(restrictFunctor h).obj M,
    (isFiniteLocallyFreeOfRank_iff _ r).1 (((isFiniteLocallyFreeOfRank_iff M r).2 hM).restrict h),
    ⟨?_⟩⟩
  refine ((Functor.mapDerivedCategoryCompIso (restrictFunctorComp h g).symm ≪≫
      Functor.mapDerivedCategoryCongr (restrictFunctorCongr hk)).app E).symm ≪≫ ?_
  exact (restrictFunctor h).mapDerivedCategory.mapIso e ≪≫
    ((restrictFunctor h).mapDerivedCategorySingleFunctor i).app M

/-! ### The open subscheme -/

/-- **The open subscheme of [stacks 0BDK].** The largest open subscheme of `X` on which the derived
module `E` is a finite locally free module of rank `r` placed in degree `i`, constructed as the
union of all the opens which carry `E` in degree `i` with rank `r`. -/
def singleDegreeRankOpen : X.Opens :=
  ⨆ V : {V : X.Opens // IsSingleDegreeRank E i r V}, (V : X.Opens)

/-- An open carrying `E` in degree `i` with rank `r` is contained in `singleDegreeRankOpen`. -/
theorem le_singleDegreeRankOpen {V : X.Opens} (hV : IsSingleDegreeRank E i r V) :
    V ≤ singleDegreeRankOpen E i r :=
  le_iSup (fun W : {W : X.Opens // IsSingleDegreeRank E i r W} => (W : X.Opens)) ⟨V, hV⟩

/-- The opens carrying `E` in degree `i` with rank `r` cover `singleDegreeRankOpen` after
restriction to it. -/
theorem iSup_preimage_singleDegreeRankOpen :
    (⨆ V : {V : X.Opens // IsSingleDegreeRank E i r V},
        (singleDegreeRankOpen E i r).ι ⁻¹ᵁ (V : X.Opens)) = ⊤ := by
  refine top_le_iff.1 fun y _ => ?_
  rw [TopologicalSpace.Opens.mem_iSup]
  have hy : (y.val : X) ∈
      (⨆ V : {V : X.Opens // IsSingleDegreeRank E i r V}, (V : X.Opens)) := y.2
  rw [TopologicalSpace.Opens.mem_iSup] at hy
  exact hy

/-- **The open subscheme of [stacks 0BDK] carries `E` in degree `i` with rank `r`.** The cohomology
sheaves of `E` vanish on it outside degree `i`, and the degree-`i` one is finite locally free of
rank `r` there. -/
theorem isSingleDegreeRank_singleDegreeRankOpen :
    IsSingleDegreeRank E i r (singleDegreeRankOpen E i r) := by
  refine ⟨fun j hj => ?_, ?_⟩
  · refine Stacks.AlgebraicGeometry.Tag01XJUniformVanishing.isZero_of_isZero_restrict
      (fun V : {V : X.Opens // IsSingleDegreeRank E i r V} =>
        (singleDegreeRankOpen E i r).ι ⁻¹ᵁ (V : X.Opens))
      (iSup_preimage_singleDegreeRankOpen E i r) _ fun V => ?_
    exact (isZero_restrict_preimage_iff (le_singleDegreeRankOpen E i r V.2) _).2 (V.2.1 j hj)
  · refine (isFiniteLocallyFreeOfRank_iff _ r).1
      (isFiniteLocallyFreeOfRank_of_iSup_eq_top
        (fun V : {V : X.Opens // IsSingleDegreeRank E i r V} =>
          (singleDegreeRankOpen E i r).ι ⁻¹ᵁ (V : X.Opens))
        (iSup_preimage_singleDegreeRankOpen E i r) fun V => ?_)
    exact (isFiniteLocallyFreeOfRank_restrict_preimage_iff
      (le_singleDegreeRankOpen E i r V.2) _ r).2 V.2.2

/-- An open of `X` carries the derived module `E` in degree `i` with rank `r` exactly when it is
contained in `singleDegreeRankOpen`. -/
theorem le_singleDegreeRankOpen_iff (V : X.Opens) :
    IsSingleDegreeRank E i r V ↔ V ≤ singleDegreeRankOpen E i r :=
  ⟨le_singleDegreeRankOpen E i r,
    fun h => IsSingleDegreeRank.mono E i r (isSingleDegreeRank_singleDegreeRankOpen E i r) h⟩

/-- **The open subscheme of [stacks 0BDK] is characterised by the first description.** An open of
`X` is contained in `singleDegreeRankOpen` exactly when the restriction of `E` to it is isomorphic
to a finite locally free module of rank `r` placed in degree `i`; so `singleDegreeRankOpen` is the
largest open subscheme on which `E` has that shape. -/
@[stacks 0BDK "the open description"]
theorem nonempty_iso_singleFunctor_restrict_iff_le (V : X.Opens) :
    (∃ M : V.toScheme.Modules,
        AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r ∧
          Nonempty ((restrictFunctor V.ι).mapDerivedCategory.obj E ≅
            (DerivedCategory.singleFunctor V.toScheme.Modules i).obj M)) ↔
      V ≤ singleDegreeRankOpen E i r :=
  (isSingleDegreeRank_iff E i r V).symm.trans (le_singleDegreeRankOpen_iff E i r V)

/-- **The cohomology of `E` vanishes outside degree `i` on the open subscheme of [stacks 0BDK].**
-/
@[stacks 0BDK "the open description"]
theorem isZero_homology_singleDegreeRankOpen (j : ℤ) (hj : j ≠ i) :
    IsZero ((DerivedCategory.homologyFunctor
        (singleDegreeRankOpen E i r).toScheme.Modules j).obj
      ((restrictFunctor (singleDegreeRankOpen E i r).ι).mapDerivedCategory.obj E)) :=
  IsZero.of_iso ((isSingleDegreeRank_singleDegreeRankOpen E i r).1 j hj)
    ((homologyFunctor_mapDerivedCategory_restrictFunctor_iso
      (singleDegreeRankOpen E i r).ι j).app E)

/-- **On the open subscheme of [stacks 0BDK] the derived module `E` is its own degree-`i`
cohomology sheaf placed in degree `i`.** This is the first half of description (1) of the tag. -/
@[stacks 0BDK "the open description"]
theorem nonempty_iso_singleFunctor_restrict_singleDegreeRankOpen :
    Nonempty ((restrictFunctor (singleDegreeRankOpen E i r).ι).mapDerivedCategory.obj E ≅
      (DerivedCategory.singleFunctor (singleDegreeRankOpen E i r).toScheme.Modules i).obj
        ((DerivedCategory.homologyFunctor
            (singleDegreeRankOpen E i r).toScheme.Modules i).obj
          ((restrictFunctor (singleDegreeRankOpen E i r).ι).mapDerivedCategory.obj E))) :=
  nonempty_iso_singleFunctor_homologyFunctor_restrict (singleDegreeRankOpen E i r).ι E i
    (isSingleDegreeRank_singleDegreeRankOpen E i r).1

/-- **On the open subscheme of [stacks 0BDK] the degree-`i` cohomology sheaf of `E` is finite
locally free of rank `r`.** This is the second half of description (1) of the tag. -/
@[stacks 0BDK "the open description"]
theorem isFiniteLocallyFreeOfRank_homology_singleDegreeRankOpen :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((DerivedCategory.homologyFunctor
          (singleDegreeRankOpen E i r).toScheme.Modules i).obj
        ((restrictFunctor (singleDegreeRankOpen E i r).ι).mapDerivedCategory.obj E)) r :=
  isFiniteLocallyFreeOfRank_homology_restrict E i r (isSingleDegreeRank_singleDegreeRankOpen E i r)

/-- **The universal property of the open subscheme of [stacks 0BDK], for open immersions.** An open
immersion `f : Y ⟶ X` factors through `singleDegreeRankOpen` exactly when the restriction of `E`
along `f` is isomorphic to a finite locally free module of rank `r` placed in degree `i`.

This is description (2) of the tag for an open immersion, with the exact restriction functor along
`f` in place of the derived pullback; the tag states it for an arbitrary morphism and the derived
pullback. -/
@[stacks 0BDK "the universal property for open immersions, restriction for the derived pullback"]
theorem factorsThrough_singleDegreeRankOpen_iff {Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] :
    (∃ g : Y ⟶ (singleDegreeRankOpen E i r).toScheme,
        g ≫ (singleDegreeRankOpen E i r).ι = f) ↔
      ∃ M : Y.Modules,
        AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r ∧
          Nonempty ((restrictFunctor f).mapDerivedCategory.obj E ≅
            (DerivedCategory.singleFunctor Y.Modules i).obj M) := by
  have hrange : (∃ g : Y ⟶ (singleDegreeRankOpen E i r).toScheme,
      g ≫ (singleDegreeRankOpen E i r).ι = f) ↔ f.opensRange ≤ singleDegreeRankOpen E i r := by
    constructor
    · rintro ⟨g, rfl⟩ x hx
      obtain ⟨y, rfl⟩ := hx
      have hmem : (g ≫ (singleDegreeRankOpen E i r).ι).base y ∈
          Set.range (singleDegreeRankOpen E i r).ι.base := ⟨g.base y, by simp⟩
      rwa [Scheme.Opens.range_ι] at hmem
    · intro hle
      refine ⟨AlgebraicGeometry.IsOpenImmersion.lift _ f ?_,
        AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ _⟩
      rwa [Scheme.Opens.range_ι]
  rw [hrange, ← le_singleDegreeRankOpen_iff, isSingleDegreeRank_iff]
  constructor
  · exact nonempty_iso_singleFunctor_restrict_of_comp E i r f.opensRange.ι
      f.isoOpensRange.hom f (Scheme.Hom.isoOpensRange_hom_ι f)
  · exact nonempty_iso_singleFunctor_restrict_of_comp E i r f f.isoOpensRange.inv
      f.opensRange.ι (Scheme.Hom.isoOpensRange_inv_comp f)

end AlgebraicGeometry.Scheme.Modules

end
