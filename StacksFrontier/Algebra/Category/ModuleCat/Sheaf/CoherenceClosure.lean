module

public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentWeakSerre
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExactnessSheafify
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Coherence is local on the base

Let `R` be a sheaf of rings on a topological space `X`. The predicate
`Stacks.SheafOfModules.IsCoherent` of Stacks 01BV is a *global* statement about a sheaf of
`R`-modules `M`: that `M` is of finite type, and that over every open `U` the kernel of every
map from a finite free module into `M|_U` is of finite type. Every proof in Stacks Section 17.21
that a sheaf is coherent — tensor products (01CE), tensor, exterior and symmetric powers (01CK),
internal homs (01CQ) — produces instead a *local* description of the sheaf, valid only on the
members of some open cover, and concludes with "and the result for coherent sheaves then follows
from Lemma 01BY". That last step is what this file supplies.

The obstruction it removes is that the closure theory of coherent sheaves
(`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentWeakSerre`) is stated over a site of the
form `Opens.grothendieckTopology X`, whereas a local description lives on the slice site
`Over U`, which is not of that form. The predicate `IsCoherentOn M W` below is the slice-free
way to say "`M` is coherent on `W`": it quantifies over the *opens below* `W` rather than over
the objects of `Over U`, so it is manifestly hereditary, and `isCoherent_of_coversTop` glues it.
The transport between the two readings — the only real content — is
`CoherentWeakSerre`'s `overOverEquivalence` together with `overOverIso`.

## Main definitions

* `Stacks.SheafOfModules.IsCoherentOn M W`: `M` is of finite type on every open `W' ≤ W`, and
  over every such `W'` the kernel of every map into `M|_{W'}` from a sheaf of modules with
  finitely many generating sections is of finite type. This is the restriction to `W` of the two
  conditions defining `IsCoherent`, phrased so that it descends to smaller opens by
  transitivity of `≤` (`IsCoherentOn.mono`) rather than by a transport along a slice
  equivalence.

## Main results

* `Stacks.SheafOfModules.coherentModules_isClosedUnderFiniteCoproducts` and
  `isCoherent_sigma`: a finite coproduct of coherent sheaves of modules is coherent. This is
  the extension-closure of Stacks 01BY (4) fed through `ObjectProperty.prop_biprod`, since in
  an additive category a binary coproduct is a biproduct.
* `Stacks.SheafOfModules.isCoherent_of_coversTop`: **coherence is local on the base.** If `M` is
  coherent on each member of a family of opens that covers `X`, then `M` is coherent. With
  `isCoherentOn_of_isCoherent` this is an equivalence, recorded as
  `isCoherent_iff_isCoherentOn_of_coversTop`: `IsCoherentOn` loses nothing.
* `Stacks.SheafOfModules.isCoherentOn_of_mono` and `isCoherent_of_coversTop_of_mono`: **a sheaf
  of modules that is locally a finite-type subsheaf of a coherent sheaf is coherent.** This is
  Stacks 01BY (1) in local form, and it is the form in which 01BY is invoked at the end of the
  proofs of 01CQ and 01CK.
* `Stacks.SheafOfModules.isCoherent_of_locallyKernelFiniteCoproduct`: a sheaf of modules that is,
  around every point, the kernel of a map between two finite direct sums of copies of a coherent
  sheaf `G` is coherent. This is the second assertion of Stacks 01CQ as a consequence of the
  first: specialized to the internal hom `SheafHom(F, G)` of a finitely presented `F` it is
  exactly "in particular, if `G` is coherent then `SheafHom(F, G)` is coherent too".

## Implementation notes

**What `IsCoherentOn` is not.** It is *not* coherence of `M.over W` as a sheaf of modules on the
site `Over W`, because `Stacks.SheafOfModules.IsCoherent` is only defined over a site of opens
of a space and `Over W` is not literally one. The two agree — `isCoherentOn_of_mono` and
`isFiniteType_kernel_over_of_isCoherentOn` are the two directions of the comparison in the
cases needed — but the agreement is a theorem about `overOverEquivalence`, not a definitional
matter, and `IsCoherentOn` is stated so that the comparison is needed once rather than at every
use. Generalizing `IsCoherent` itself to an arbitrary site, which would make `IsCoherentOn W`
literally `IsCoherent (M.over W)`, is the structurally better fix and is not done here.

**Universes.** Everything is equi-universe: the space is `X : Type u`, the site is `Opens X`
with `Category.{u}`, the sheaf of rings is `RingCat.{u}`-valued and the modules are
`SheafOfModules.{u}`. This is forced, not chosen: the whole coherence substrate this file builds
on (`Coherent.lean`, `CoherentWeakSerre.lean`) is stated that way, and the gluing step goes
through `LocalKernel.isFiniteType_of_coversTop`, whose index type lives in the universe of the
site. The index type of the covering family in `isCoherent_of_coversTop` is correspondingly
`I : Type u`; in `isCoherent_of_locallyKernelFiniteCoproduct` it is `X` itself, so no shrinking
is needed.

**The finite direct sums are indexed by `Fin m`, not by an arbitrary finite type.** That is the
shape Stacks 01CQ states and the shape the finite presentation of `F` produces, and
`isCoherent_sigma` is stated for an arbitrary finite index type so that both are available;
`Fin m` lives in `Type 0` while the sheaves live in universe `u`, which is why the index type of
`isCoherent_sigma` is `Type*` and not `Type u`.

**The coproduct trio is duplicated in `CoherentSite.lean`, and is not the copy to delete.**
`coherentModules_isClosedUnderBinaryCoproducts`, `coherentModules_isClosedUnderFiniteCoproducts`
and `isCoherent_sigma` below appear verbatim — same docstrings, same proof bodies — as
`Stacks.SheafOfModules.Site.*` in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentSite`, whose section is quantified over an
arbitrary `{J} {R}` and so looks like it subsumes these. It does not: those statements are about
`Site.IsCoherent`, a constant distinct from `Stacks.SheafOfModules.IsCoherent`, that file imports
*this* one, and `isCoherent_of_locallyKernelFiniteCoproduct` below uses `isCoherent_sigma`, so
routing this file at the general forms is an import cycle. `CoherentSite.lean`'s implementation
notes carry the full argument.

**The ambient sheaf is the source of the map, not its target.** In
`isCoherent_of_locallyKernelFiniteCoproduct` the mono exhibiting `M|_U` as a subsheaf is into the
`m`-fold sum, since `kernel.ι f` lands in the domain of `f`; the `n`-fold sum is used only to
see that the kernel is of finite type.

## References

* [Stacks Project, Tag 01BV](https://stacks.math.columbia.edu/tag/01BV)
* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
* [Stacks Project, Tag 01CQ](https://stacks.math.columbia.edu/tag/01CQ)
-/

@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace SheafOfModules

universe u

namespace Stacks.SheafOfModules

/-! ### Finite coproducts of coherent sheaves of modules -/

section FiniteCoproducts

variable {X : Type u} [TopologicalSpace X]
  {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}

/-- Coherent sheaves of modules are closed under binary coproducts: a binary coproduct in an
additive category is a biproduct, hence an extension of one summand by the other, and coherent
sheaves are closed under extensions by Stacks 01BY (4). -/
instance coherentModules_isClosedUnderBinaryCoproducts :
    (coherentModules R).IsClosedUnderBinaryCoproducts :=
  ObjectProperty.IsClosedUnderColimitsOfShape.mk' (by
    rintro _ ⟨F, hF⟩
    exact (coherentModules R).prop_of_iso
      ((biprod.isoCoprod (F.obj ⟨WalkingPair.left⟩) (F.obj ⟨WalkingPair.right⟩)).trans
        (HasColimit.isoOfNatIso (diagramIsoPair F)).symm)
      ((coherentModules R).prop_biprod (hF ⟨WalkingPair.left⟩) (hF ⟨WalkingPair.right⟩)))

/-- Coherent sheaves of modules are closed under finite coproducts: they contain the zero object
and are closed under binary coproducts. -/
instance coherentModules_isClosedUnderFiniteCoproducts :
    (coherentModules R).IsClosedUnderFiniteCoproducts :=
  ObjectProperty.IsClosedUnderFiniteCoproducts.mk'

/-- A finite direct sum of coherent sheaves of modules is coherent. -/
@[ega "0 5.3.2"]
theorem isCoherent_sigma {J : Type*} [Finite J] (f : J → SheafOfModules.{u} R)
    [HasCoproduct f] (hf : ∀ j, IsCoherent (f j)) : IsCoherent (∐ f) :=
  (coherentModules R).prop_coproduct hf

end FiniteCoproducts

/-! ### Transport of finite type along the iterated slice equivalence -/

section IteratedSlice

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasFiniteWidePullbacks C] [HasPullbacks C] [HasBinaryProducts C]
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ Y : C, HasSheafify (J.over Y) AddCommGrpCat.{u}]
  [∀ Y : C, (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (Y : C) (Z : Over Y), HasSheafify ((J.over Y).over Z) AddCommGrpCat.{u}]
  [∀ (Y : C) (Z : Over Y), ((J.over Y).over Z).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (Y : C) (Z : Over Y) (W : Over Z),
    HasSheafify (((J.over Y).over Z).over W) AddCommGrpCat.{u}]
  [∀ (Y : C) (Z : Over Y) (W : Over Z),
    (((J.over Y).over Z).over W).WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [HasFiniteWidePullbacks C] [HasBinaryProducts C] [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ Y : C, HasSheafify (J.over Y) AddCommGrpCat.{u}]
  [∀ Y : C, (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Being of finite type transports from the iterated slice site at `Z` down to the slice site at
`Z.left`. This is the direction opposite to `isFiniteType_of_overOverEquivalence_inverse`, and
like it, it is `isFiniteType_pushforward` for the functor underlying the slice equivalence — here
for its inverse. -/
theorem isFiniteType_overOverEquivalence_inverse_obj (U : C) (Z : Over U)
    {N : SheafOfModules.{u} ((R.over U).over Z)} (h : N.IsFiniteType) :
    ((overOverEquivalence U Z (R := R)).inverse.obj N).IsFiniteType :=
  have := h
  isFiniteType_pushforward (G := (Over.iteratedSliceEquiv Z).inverse) (𝟙 _) (Iso.refl _)

end IteratedSlice

/-! ### Coherence on an open, and its locality -/

section Locality

variable {X : Type u} [TopologicalSpace X]
  {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}

/-- `M` is **coherent on the open `W`** if over every open `W' ≤ W` the restriction `M|_{W'}` is
of finite type and the kernel of every morphism into `M|_{W'}` from a sheaf of modules with
finitely many generating sections is of finite type.

These are the two conditions of Stacks 01BV, restricted to the opens below `W`. Quantifying over
opens of `X` below `W` rather than over the objects of the slice site `Over W` is what makes the
predicate hereditary on the nose (`IsCoherentOn.mono`); the comparison with the slice reading is
`isFiniteType_kernel_over_of_isCoherentOn`. -/
def IsCoherentOn (M : SheafOfModules.{u} R) (W : Opens X) : Prop :=
  ∀ W' : Opens X, W' ≤ W →
    (M.over W').IsFiniteType ∧
      ∀ (N : SheafOfModules.{u} (R.over W')) (σ : N.GeneratingSections), Finite σ.I →
        ∀ g : N ⟶ M.over W', (kernel g).IsFiniteType

/-- Coherence on an open passes to smaller opens. -/
theorem IsCoherentOn.mono {M : SheafOfModules.{u} R} {W W' : Opens X}
    (h : IsCoherentOn M W) (hW : W' ≤ W) : IsCoherentOn M W' :=
  fun W'' hW'' => h W'' (hW''.trans hW)

/-- A coherent sheaf of modules is coherent on every open: restriction preserves finite type,
and the kernel condition over an open is Stacks 01BY (2) in the relative form
`isFiniteType_kernel_of_generatingSections`. -/
theorem isCoherentOn_of_isCoherent (M : SheafOfModules.{u} R) [IsCoherent M] (W : Opens X) :
    IsCoherentOn M W := fun W' _ =>
  ⟨isFiniteType_over_of_isFiniteType W', fun _ σ hσ g =>
    have := hσ
    isFiniteType_kernel_of_generatingSections W' σ g⟩

/-- The slice reading of `IsCoherentOn`: if `M` is coherent on `W` then for every open `U`, every
finite free module over the slice site at `U` and every morphism `φ` from it into `M|_U`, the
kernel of `φ` restricted to an object `Z` of the slice site lying over `W` is of finite type.

This is the transport that `IsCoherentOn` exists to confine to one place: the restriction of `φ`
to `Z` is carried along `overOverEquivalence U Z` to a morphism into `M|_{Z.left}`, where the
hypothesis applies, and carried back along `PreservesKernel.iso` and `overKernelIso`. -/
theorem isFiniteType_kernel_over_of_isCoherentOn {M : SheafOfModules.{u} R} {W : Opens X}
    (hW : IsCoherentOn M W) (U : Opens X) {A : Type u} [Finite A]
    (φ : (free A : SheafOfModules.{u} (R.over U)) ⟶ M.over U) (Z : Over U) (hZ : Z.left ≤ W) :
    ((kernel φ).over Z).IsFiniteType := by
  have key : (kernel (φ.over Z)).IsFiniteType := by
    let e := overOverEquivalence (R := R) U Z
    let τ : ((free A : SheafOfModules.{u} (R.over U)).over Z).GeneratingSections :=
      (free.generatingSections (R := R.over U) A).map (overFunctor (R.over U) Z) (by rfl)
    let σ := τ.map e.inverse (Iso.refl (unit (R.over Z.left)))
    have hfin : Finite σ.I := inferInstanceAs (Finite A)
    have h2 := (hW Z.left hZ).2 _ σ hfin
      (e.inverse.map (φ.over Z) ≫ (overOverIso M U Z).hom)
    have h3 : (kernel (e.inverse.map (φ.over Z))).IsFiniteType :=
      isFiniteType_of_iso.{u}
        (M := kernel (e.inverse.map (φ.over Z) ≫ (overOverIso M U Z).hom))
        (N := kernel (e.inverse.map (φ.over Z)))
        (kernel.mapIso _ (e.inverse.map (φ.over Z))
          (Iso.refl _) (overOverIso M U Z).symm (by simp))
    have h4 : (e.inverse.obj (kernel (φ.over Z))).IsFiniteType :=
      isFiniteType_of_iso.{u} (PreservesKernel.iso e.inverse (φ.over Z)).symm
    exact isFiniteType_of_overOverEquivalence_inverse U Z h4
  exact isFiniteType_of_iso.{u} (overKernelIso φ Z).symm

/-- **Coherence is local on the base.** A sheaf of modules that is coherent on every member of a
family of opens covering the space is coherent.

Both conditions of Stacks 01BV are checked by gluing: finite type by
`LocalKernel.isFiniteType_of_coversTop` on the base, and the kernel condition over an open `U` by
the same gluing on the slice site at `U`, over the covering family of those objects of `Over U`
that lie over a member of the given cover. -/
theorem isCoherent_of_coversTop (M : SheafOfModules.{u} R) {I : Type u} (V : I → Opens X)
    (hV : (Opens.grothendieckTopology X).CoversTop V)
    (hM : ∀ i, IsCoherentOn M (V i)) : IsCoherent M where
  isFiniteType :=
    LocalKernel.isFiniteType_of_coversTop M V hV fun i => (hM i (V i) le_rfl).1
  kernel_isFiniteType U A hA φ := by
    have := hA
    have hcover : ((Opens.grothendieckTopology X).over U).CoversTop
        (Subtype.val : { Z : Over U // ((kernel φ).over Z).IsFiniteType } → Over U) := by
      intro Y
      refine ((Opens.grothendieckTopology X).over U).superset_covering ?_
        ((Over.forget U).cover_lift ((Opens.grothendieckTopology X).over U)
          (Opens.grothendieckTopology X) (hV Y.left))
      intro Z g hg
      obtain ⟨i, ⟨h⟩⟩ := (Sieve.mem_ofObjects_iff _ ((Over.forget U).map g)).1 hg
      exact (Sieve.mem_ofObjects_iff _ g).2
        ⟨⟨Z, isFiniteType_kernel_over_of_isCoherentOn (hM i) U φ Z (leOfHom h)⟩, ⟨𝟙 Z⟩⟩
    exact LocalKernel.isFiniteType_of_coversTop (kernel φ) Subtype.val hcover fun i => i.2

/-- Coherence is *equivalent* to coherence on the members of a cover: `IsCoherentOn` is neither
weaker nor stronger than what `IsCoherent` says locally. -/
theorem isCoherent_iff_isCoherentOn_of_coversTop (M : SheafOfModules.{u} R) {I : Type u}
    (V : I → Opens X) (hV : (Opens.grothendieckTopology X).CoversTop V) :
    IsCoherent M ↔ ∀ i, IsCoherentOn M (V i) :=
  ⟨fun h i => have := h; isCoherentOn_of_isCoherent M (V i), isCoherent_of_coversTop M V hV⟩

end Locality

/-! ### Locally a subsheaf of a coherent sheaf -/

section LocalSubsheaf

variable {X : Type u} [TopologicalSpace X]
  {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}

/-- A finite type subsheaf of the restriction of a coherent sheaf of modules to an open `W` is
coherent on `W`.

This is Stacks 01BY (1) relative to `W`: the mono and the finite type hypothesis are restricted
further to each open `W' ≤ W` along `overOverEquivalence`, and then a morphism into `M|_{W'}`
from a sheaf with finitely many generating sections has the same kernel as its composite into
`P|_{W'}`, which is of finite type by coherence of `P`. -/
theorem isCoherentOn_of_mono {M P : SheafOfModules.{u} R} [IsCoherent P] {W : Opens X}
    (hft : (M.over W).IsFiniteType) (ι : M.over W ⟶ P.over W) [Mono ι] :
    IsCoherentOn M W := by
  intro W' hW'
  have := hft
  let Z : Over W := Over.mk (homOfLE hW')
  let e := overOverEquivalence (R := R) W Z
  have hMZ : ((M.over W).over Z).IsFiniteType := isFiniteType_over_of_isFiniteType Z
  have hMZ' : (e.inverse.obj ((M.over W).over Z)).IsFiniteType :=
    isFiniteType_overOverEquivalence_inverse_obj W Z hMZ
  have hft' : (M.over W').IsFiniteType := isFiniteType_of_iso.{u} (overOverIso M W Z)
  have hmono : Mono (ι.over Z) := over_mono ι Z
  let ι' : M.over W' ⟶ P.over W' :=
    (overOverIso M W Z).inv ≫ e.inverse.map (ι.over Z) ≫ (overOverIso P W Z).hom
  have : Mono ι' := by
    have : Mono (e.inverse.map (ι.over Z)) := inferInstance
    exact mono_comp _ _
  refine ⟨hft', fun N σ hσ g => ?_⟩
  have := hσ
  have hk : (kernel (g ≫ ι')).IsFiniteType :=
    isFiniteType_kernel_of_generatingSections W' σ (g ≫ ι')
  exact isFiniteType_of_iso.{u} (kernelCompMono g ι')

/-- **A sheaf of modules that is locally a finite type subsheaf of a coherent sheaf of modules is
coherent.** This is Stacks 01BY (1) in the local form in which the proofs of Stacks 01CK and
01CQ invoke it: the coherent sheaf `P i` and the mono are allowed to depend on the member of the
cover. -/
theorem isCoherent_of_coversTop_of_mono (M : SheafOfModules.{u} R) {I : Type u}
    (V : I → Opens X) (hV : (Opens.grothendieckTopology X).CoversTop V)
    (P : I → SheafOfModules.{u} R) (hP : ∀ i, IsCoherent (P i))
    (hft : ∀ i, (M.over (V i)).IsFiniteType)
    (ι : ∀ i, M.over (V i) ⟶ (P i).over (V i)) (hι : ∀ i, Mono (ι i)) :
    IsCoherent M :=
  isCoherent_of_coversTop M V hV fun i =>
    have := hP i
    have := hι i
    isCoherentOn_of_mono (hft i) (ι i)

/-- **A sheaf of modules that is locally the kernel of a map between finite direct sums of copies
of a coherent sheaf of modules is coherent.**

This is the second assertion of Stacks 01CQ as a consequence of the first. The kernel of
`f : G|_U^m ⟶ G|_U^n` is a subsheaf of `G|_U^m = (G^m)|_U`, which is coherent by
`isCoherent_sigma`, and it is of finite type by Stacks 01BY (2) applied to `f` read as a morphism
into `(G^n)|_U`; so `isCoherent_of_coversTop_of_mono` applies. -/
theorem isCoherent_of_locallyKernelFiniteCoproduct {M G : SheafOfModules.{u} R} [IsCoherent G]
    (h : ∀ x : X, ∃ U : Opens X, x ∈ U ∧ ∃ (m n : ℕ)
      (f : (∐ fun _ : Fin m => G.over U) ⟶ (∐ fun _ : Fin n => G.over U)),
        Nonempty (M.over U ≅ kernel f)) :
    IsCoherent M := by
  choose U hU m n f ε using h
  have hV : (Opens.grothendieckTopology X).CoversTop U := by
    refine (Opens.coversTop_iff X U).2 (TopologicalSpace.IsOpenCover.mk ?_)
    ext y
    simpa using ⟨y, hU y⟩
  have hco : ∀ (x : X) (k : ℕ), IsCoherent (∐ fun _ : Fin k => G) :=
    fun _ _ => isCoherent_sigma _ fun _ => inferInstance
  refine isCoherent_of_coversTop_of_mono M U hV
    (fun x => ∐ fun _ : Fin (m x) => G) (fun x => hco x (m x)) ?_ ?_ ?_
  · intro x
    have h1 : IsCoherent (∐ fun _ : Fin (m x) => G) := hco x (m x)
    have h2 : IsCoherent (∐ fun _ : Fin (n x) => G) := hco x (n x)
    have h3 : ((∐ fun _ : Fin (m x) => G).over (U x)).IsFiniteType :=
      have : (∐ fun _ : Fin (m x) => G).IsFiniteType := IsCoherent.isFiniteType
      isFiniteType_over_of_isFiniteType (U x)
    have h4 : (∐ fun _ : Fin (m x) => G.over (U x)).IsFiniteType :=
      isFiniteType_of_iso.{u}
        (PreservesCoproduct.iso (overFunctor R (U x)) fun _ : Fin (m x) => G)
    have h5 : (kernel (f x ≫ (PreservesCoproduct.iso (overFunctor R (U x))
        fun _ : Fin (n x) => G).inv)).IsFiniteType :=
      isFiniteType_kernel_over_of_isCoherent (U x) _
    have h6 : (kernel (f x)).IsFiniteType :=
      isFiniteType_of_iso.{u} (kernelCompMono (f x)
        (PreservesCoproduct.iso (overFunctor R (U x)) fun _ : Fin (n x) => G).inv)
    exact isFiniteType_of_iso.{u} (ε x).some.symm
  · exact fun x => (ε x).some.hom ≫ kernel.ι (f x) ≫
      (PreservesCoproduct.iso (overFunctor R (U x)) fun _ : Fin (m x) => G).inv
  · intro x
    have : Mono (ε x).some.hom := inferInstance
    infer_instance

end LocalSubsheaf

end Stacks.SheafOfModules

end
