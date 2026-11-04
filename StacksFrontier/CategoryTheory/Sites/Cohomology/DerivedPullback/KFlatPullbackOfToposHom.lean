module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackShortExactFlat
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.KFlatPullbackCyclesInput
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionFactsOfSize
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOfSize
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.AdjunctionForRingedTopoi
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.PullbackAdjunction
import StacksCore.Tactic.StacksAttribute

/-!
# Pullback of K-flat complexes along an arbitrary morphism of ringed topoi

Let `f : (Sh(C'), O') ⟶ (Sh(C), O)` be a morphism of ringed topoi and let `K^•` be a K-flat
complex of `O`-modules whose terms are flat.  **Stacks 0G7E** asserts that `f^*K^•` is a K-flat
complex of `O'`-modules whose terms are flat.  This file proves both clauses with the geometric
datum an `AlgebraicGeometry.RingedToposHom` — a morphism of the underlying topoi together with
the structure map — so that no functor between the underlying sites is asked for.

The pullback is the one of Stacks 03D6 part (2),
`Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules`, namely `f^* = O' ⊗_{f⁻¹O}
f⁻¹(-)`.

## Main results

* `Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom.isFlat_pullbackComplex_X`: the
  flat-terms clause, one application of Stacks 05VD per degree.
* `Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom.kFlat_pullbackComplex`: the
  K-flatness clause.
* `Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom.isKFlat_pullbackMapHomotopy`:
  **Stacks 0G7E** read on the unbounded homotopy category, as stability of the class
  `Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat` under degreewise pullback.

## Implementation notes

*Why the three deferred inputs of the ringed-site chain are discharged here.*
`Stacks.Sheaves.DerivedPullback.KFlatPullback.kFlat_pullbackComplex` is stated for
`AlgebraicGeometry.RingedToposSiteHom.pullbackTopos` and carries Stacks 05VD and Stacks 0G6R as
the `Prop` parameters `PullbackPreservesIsFlat` and `PullbackPreservesShortExact`, each with a
`CategoryTheory.Functor.IsMorphismOfSites` hypothesis in it.  That hypothesis is an artefact of
the *presentation*: `AlgebraicGeometry.RingedToposSiteHom.pullbackTopos` is Mathlib's pullback of
sheaves of modules, an abstract left adjoint, and identifying its geometric factor with the
inverse image of sheaves of sets is a Beck--Chevalley comparison that needs a morphism of sites.
For `Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules` that comparison is
definitional, because the
functor is *constructed* from the inverse image of Stacks 03D2; left exactness of `f⁻¹` is a
field of `AlgebraicGeometry.MorphismOfTopoi` and hence available unconditionally.  So both inputs
are already theorems here — `Stacks.Sheaves.RingedToposModules.isFlat_pullbackModules` (05VD) and
`Stacks.Sheaves.RingedToposModules.shortExact_map_pullbackModules` (0G6R) — and the third input,
Stacks 0G7C, is `Stacks.Sheaves.DerivedPullback.KFlatPullback.cyclesIsFlat`, which mentions no
morphism at all.

*What is reused rather than restated.*  The two steps of the source's argument that are about the
target ringed topos alone are taken from the ringed-site development unchanged:
`Stacks.Sheaves.DerivedPullback.KFlatPullback.isFlat_truncLE_X` for the terms of a canonical
truncation, and `Stacks.Sheaves.DerivedPullback.KFlatPullback.kernelSequence_resolution_facts`
for the kernel of a resolution.  Only the seven statements that mention `f^*` are restated.

*The shape of the argument*, which is the source's.  A K-flat complex `K` with flat terms is
resolved by Stacks 06YS as a termwise surjective quasi-isomorphism `α : Λ ⟶ K` out of the colimit
`Λ` of a sequence of bounded above complexes of flat modules; that presentation, rather than
K-flatness of `Λ`, is what survives `f^*`.  The kernel `M` of `α` is acyclic, K-flat and has flat
terms, so its cycles are flat by Stacks 0G7C and `f^*M` is K-flat through the canonical
truncations; `f^*Λ` is K-flat because `f^*` commutes with the colimit degreewise; and pulling the
kernel sequence back keeps it short exact by Stacks 0G6R, whence `f^*K` is K-flat by Stacks 0G7B.

*Universes.*  Both ringed topoi are at `AlgebraicGeometry.RingedTopos.{u, u, u}`.  The narrowing
is inherited, but **not** from Stacks 06YS: that is
`Stacks.SheafOfModules.KFlatResolution.exists_kFlatResolution_ofSize`, whose three universes are
independent, and the class it resolves,
`Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat`, is stated at independent
universes too, so both reach an `AlgebraicGeometry.RingedTopos.{u, u + 1, u}`.  What narrows this
file is the pair of inputs named above.  Writing `RingedTopos.{v₁, u₁, w₁}` for morphisms,
objects and sections, `Stacks.Sheaves.RingedToposModules.isFlat_pullbackModules` (05VD) and
`Stacks.Sheaves.RingedToposModules.shortExact_map_pullbackModules` (0G6R) are stated for
`Y : RingedTopos.{v', u', max u' v'}` and `X : RingedTopos.{v, max u v, max u v}`, so the section
universe of each must dominate its site universes; a site whose objects lie *above* the sections
is not an instance of either, and no instantiation exists, `max (u + 1) u` being `u + 1` and not
`u`.  Their own narrowing is recorded in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PullbackFlatInverseImage.lean` and comes from the
local equational criterion of Stacks 08FC, which is written at `max u v` throughout and needs
`CategoryTheory.HasSheafify` for `Type`-valued sheaves at the section universe.  Stacks 0G7C
(`Stacks.Sheaves.DerivedPullback.KFlatPullback.cyclesIsFlat`), Stacks 0G7B
(`Stacks.SheafOfModules.KFlatTwoOutOfThree.kFlat_right_of_shortExact`) and the two reused steps
`isFlat_truncLE_X` and `kernelSequence_resolution_facts` are pinned to one universe as well, each
independently of the others.  Unlike the ringed-site chain nothing here is narrowed by
`CategoryTheory.Functor.IsMorphismOfSites`, which is available only for two small categories in
one and the same universe.

## References

* [Stacks Project, Tag 0G7E](https://stacks.math.columbia.edu/tag/0G7E)
* [Stacks Project, Tag 05VD](https://stacks.math.columbia.edu/tag/05VD)
* [Stacks Project, Tag 0G6R](https://stacks.math.columbia.edu/tag/0G6R)
* [Stacks Project, Tag 0G7C](https://stacks.math.columbia.edu/tag/0G7C)
* [Stacks Project, Tag 0G7B](https://stacks.math.columbia.edu/tag/0G7B)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u w v' u' w'

namespace Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom

open AlgebraicGeometry.RingedToposHom
open Stacks.SheafOfModules.KFlatOfSize (isFlat_truncLE_X_ofSize
  kernelSequence_resolution_facts_ofSize)

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasSheafify X.J (Type w)] [HasSheafify Y.J (Type w')]

/-- The degreewise pullback of complexes of modules along a morphism of ringed topoi, the functor
on complexes that Stacks 0G7E is a statement about. -/
abbrev pullbackComplex (f : RingedToposHom X Y) :
    CochainComplex (SheafOfModules.{w'} (SheafOfModules.Tensor.ringSheaf Y.O)) ℤ ⥤
      CochainComplex (SheafOfModules.{w} (SheafOfModules.Tensor.ringSheaf X.O)) ℤ :=
  (f.toModulesHom.pullbackModules).mapHomologicalComplex (ComplexShape.up ℤ)

/-! ### The two inputs, unconditional for a morphism of the underlying topoi -/

/-- **Stacks 05VD** for the pullback of Stacks 03D6 part (2): the pullback of a flat sheaf of
modules along a morphism of ringed topoi is flat.  The inverse image of a morphism of topoi is
exact by definition, so no hypothesis on the underlying sites intervenes. -/
@[sga "4 V 1.7.1" "special case"]
theorem isFlat_pullbackModules_obj (f : RingedToposHom X Y)
    (M : SheafOfModules.{w'} (SheafOfModules.Tensor.ringSheaf Y.O))
    (hM : AlgebraicGeometry.SheafOfModules.IsFlat.{v', u', w', w'} (O := Y.O) M) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := X.O)
      ((f.toModulesHom.pullbackModules).obj M) :=
  Stacks.Sheaves.RingedToposModules.isFlat_pullbackModules f.toModulesHom M hM

/-- **Stacks 0G6R** for the pullback of Stacks 03D6 part (2): pullback along a morphism of ringed
topoi keeps a short exact sequence of modules short exact when its third term is flat. -/
theorem shortExact_map_pullbackModules (f : RingedToposHom X Y)
    (S : ShortComplex (SheafOfModules.{w'} (SheafOfModules.Tensor.ringSheaf Y.O)))
    (hS : S.ShortExact)
    (hflat : AlgebraicGeometry.SheafOfModules.IsFlat.{v', u', w', w'} (O := Y.O) S.X₃) :
    (S.map (f.toModulesHom.pullbackModules)).ShortExact :=
  Stacks.Sheaves.RingedToposModules.shortExact_map_pullbackModules f.toModulesHom S hS hflat

/-! ### The flat-terms clause of Stacks 0G7E -/

/-- **The flat-terms clause of Stacks 0G7E.**  The degree `i` term of `f^*K` is `f^*(K^i)` on the
nose, so the content is one application of Stacks 05VD per degree and nothing about
K-flatness. -/
theorem isFlat_pullbackComplex_X (f : RingedToposHom X Y)
    (K : CochainComplex (SheafOfModules.{w'} (SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hflatK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{v', u', w', w'} (O := Y.O) (K.X i))
    (i : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := X.O)
      (((pullbackComplex f).obj K).X i) :=
  isFlat_pullbackModules_obj f _ (hflatK i)

/-! ### The engine: what the pullback does to a colimit of bounded above flat complexes -/

omit [HasSheafify X.J (Type w)] [HasSheafify Y.J (Type w')]
  [HasSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- The degreewise pullback of a complex bounded above by `b` is bounded above by `b`, since
`f^*` carries a zero module to a zero module. -/
lemma isStrictlyLE_pullbackComplex (f : RingedToposHom X Y)
    (L : CochainComplex (SheafOfModules.{w'} (SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) (b : ℤ)
    [L.IsStrictlyLE b] : ((pullbackComplex f).obj L).IsStrictlyLE b := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact Functor.map_isZero (f.toModulesHom.pullbackModules) (L.isZero_of_isStrictlyLE b i hi)

/-- The pullback of a bounded above complex of flat modules is K-flat: its terms are flat by
Stacks 05VD and it is still bounded above, so Stacks 06YQ applies. -/
theorem kFlat_pullbackComplex_of_isStrictlyLE (f : RingedToposHom X Y)
    (L : CochainComplex (SheafOfModules.{w'} (SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) (b : ℤ)
    [L.IsStrictlyLE b]
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{v', u', w', w'} (O := Y.O) (L.X i)) :
    Stacks.SheafOfModules.KFlat.KFlat X.O ((pullbackComplex f).obj L) := by
  have : ((pullbackComplex f).obj L).IsStrictlyLE b := isStrictlyLE_pullbackComplex f L b
  refine CochainComplex.KFlatBifunctor.kFlat_of_isStrictlyLE _ _ b
    (Stacks.SheafOfModules.KFlatResolution.hF_sheafTensor_ofSize X.O)
      (Stacks.SheafOfModules.KFlatResolution.hexact_sheafOfModules_ofSize X.O) fun q ↦ ?_
  exact Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat_ofSize X.O _
    (isFlat_pullbackComplex_X f L hflat q) q

/-- **The engine.**  The pullback of a sequential colimit of bounded above complexes of flat
modules is K-flat: `f^*` is a left adjoint, so it commutes with the colimit degreewise, and each
stage pulls back to a bounded above complex of flat modules. -/
theorem kFlat_pullbackComplex_of_isColimit (f : RingedToposHom X Y)
    (D : ℕ ⥤ CochainComplex (SheafOfModules.{w'} (SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (c : Cocone D) (hc : IsColimit c)
    (hLE : ∀ n : ℕ, ∃ b : ℤ, (D.obj n).IsStrictlyLE b)
    (hflat : ∀ (n : ℕ) (i : ℤ), AlgebraicGeometry.SheafOfModules.IsFlat.{v', u', w', w'}
      (O := Y.O) ((D.obj n).X i)) :
    Stacks.SheafOfModules.KFlat.KFlat X.O ((pullbackComplex f).obj c.pt) := by
  have : PreservesColimitsOfSize.{0, 0} (f.toModulesHom.pullbackModules) :=
    (pullbackAdjPushforwardModules f).leftAdjoint_preservesColimits
  have hp := CochainComplex.KFlat.preservesColimit_mapHomologicalComplex D
    f.toModulesHom.pullbackModules
  refine CochainComplex.KFlatBifunctor.kFlat_of_isColimit _
    ((pullbackComplex f).mapCocone c) (isColimitOfPreserves (pullbackComplex f) hc)
    (Stacks.SheafOfModules.KFlatResolution.hF_sheafTensor_ofSize X.O)
      (Stacks.SheafOfModules.KFlatResolution.hexact_sheafOfModules_ofSize X.O) fun n ↦ ?_
  obtain ⟨b, hb⟩ := hLE n
  exact kFlat_pullbackComplex_of_isStrictlyLE f (D.obj n) b (hflat n)

/-- The pullback of a complex with flat terms and flat cycles is K-flat: such a complex is the
sequential colimit of its canonical truncations, each of which is bounded above with flat terms,
so the engine applies.  This is the acyclic case of the source's argument; acyclicity itself is
used only to know that the cycles are flat (Stacks 0G7C). -/
theorem kFlat_pullbackComplex_of_isFlat_cycles (f : RingedToposHom X Y)
    (M : CochainComplex (SheafOfModules.{w'} (SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{v', u', w', w'} (O := Y.O) (M.X i))
    (hcyc : ∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{v', u', w', w'} (O := Y.O)
      (M.cycles n)) :
    Stacks.SheafOfModules.KFlat.KFlat X.O ((pullbackComplex f).obj M) :=
  kFlat_pullbackComplex_of_isColimit f
    (Stacks.SheafOfModules.truncLESequence M) (Stacks.SheafOfModules.truncLECocone M)
    (Stacks.SheafOfModules.truncLECocone_isColimit M)
    (fun n ↦ ⟨(n : ℤ), inferInstanceAs ((M.truncLE (n : ℤ)).IsStrictlyLE (n : ℤ))⟩)
    (fun n i ↦ isFlat_truncLE_X_ofSize Y.O M hflat hcyc (n : ℤ) i)

/-- **The acyclic case of Stacks 0G7E.**  The pullback of an acyclic K-flat complex with flat
terms is K-flat: Stacks 0G7C makes its cycles flat, and flat cycles are all that the engine
needs. -/
theorem kFlat_pullbackComplex_of_acyclic (f : RingedToposHom X Y)
    (M : CochainComplex (SheafOfModules.{w'} (SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hacyc : M.Acyclic) (hM : Stacks.SheafOfModules.KFlat.KFlat Y.O M)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{v', u', w', w'} (O := Y.O) (M.X i)) :
    Stacks.SheafOfModules.KFlat.KFlat X.O ((pullbackComplex f).obj M) :=
  kFlat_pullbackComplex_of_isFlat_cycles f M hflat
    (Stacks.Sheaves.DerivedPullback.KFlatPullback.cyclesIsFlat Y M hacyc hM hflat)

/-! ### The K-flatness clause of Stacks 0G7E -/

/-- Pullback of a short exact sequence of complexes whose third complex has flat terms is short
exact, degree by degree, by Stacks 0G6R. -/
theorem shortExact_map_pullbackComplex (f : RingedToposHom X Y)
    (S : ShortComplex
      (CochainComplex (SheafOfModules.{w'} (SheafOfModules.Tensor.ringSheaf Y.O)) ℤ))
    (hS : S.ShortExact)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{v', u', w', w'} (O := Y.O)
      (S.X₃.X i)) :
    (S.map (pullbackComplex f)).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i ↦ ?_
  exact shortExact_map_pullbackModules f (S.map (HomologicalComplex.eval _ (ComplexShape.up ℤ) i))
    (hS.map_of_exact (HomologicalComplex.eval _ (ComplexShape.up ℤ) i)) (hflat i)

/-- **The two-out-of-three step.**  For a short exact sequence `0 ⟶ S₁ ⟶ S₂ ⟶ S₃ ⟶ 0` of
complexes of `O`-modules with `S₃` of flat terms, `f^*S₃` is K-flat as soon as `f^*S₁` and
`f^*S₂` are: the pulled-back sequence is still short exact by Stacks 0G6R, and Stacks 0G7B gives
the third term. -/
theorem kFlat_pullbackComplex_of_shortExact (f : RingedToposHom X Y)
    (S : ShortComplex
      (CochainComplex (SheafOfModules.{w'} (SheafOfModules.Tensor.ringSheaf Y.O)) ℤ))
    (hS : S.ShortExact)
    (hflat₃ : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{v', u', w', w'} (O := Y.O)
      (S.X₃.X i))
    (h₁ : Stacks.SheafOfModules.KFlat.KFlat X.O ((pullbackComplex f).obj S.X₁))
    (h₂ : Stacks.SheafOfModules.KFlat.KFlat X.O ((pullbackComplex f).obj S.X₂)) :
    Stacks.SheafOfModules.KFlat.KFlat X.O ((pullbackComplex f).obj S.X₃) :=
  Stacks.SheafOfModules.KFlatTwoOutOfThree.kFlat_right_of_shortExact X.O
    (S.map (pullbackComplex f)) (shortExact_map_pullbackComplex f S hS hflat₃)
    (isFlat_pullbackComplex_X f _ hflat₃) h₁ h₂

/-- **The K-flatness clause of Stacks 0G7E.**  The pullback of a K-flat complex of `O`-modules
with flat terms along a morphism of ringed topoi is a K-flat complex of `O'`-modules.

The complex is resolved by Stacks 06YS out of a colimit of bounded above flat complexes; the
kernel of that resolution is acyclic, K-flat and termwise flat, so both outer terms of the kernel
sequence have K-flat pullback, and the two-out-of-three step gives the third. -/
theorem kFlat_pullbackComplex (f : RingedToposHom X Y)
    (K : CochainComplex (SheafOfModules.{w'} (SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : Stacks.SheafOfModules.KFlat.KFlat Y.O K)
    (hflatK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{v', u', w', w'} (O := Y.O)
      (K.X i)) :
    Stacks.SheafOfModules.KFlat.KFlat X.O ((pullbackComplex f).obj K) := by
  obtain ⟨D, α, hLE, hDflat, hqis, hepi⟩ :=
    Stacks.SheafOfModules.KFlatResolution.exists_resolution_colimit_ofSize Y.O K
  obtain ⟨hS, hMflat, hMkflat, hMacyc⟩ :=
    kernelSequence_resolution_facts_ofSize Y.O hK hflatK
      (Stacks.SheafOfModules.KFlatResolution.isFlat_colimit_X_ofSize Y.O D hDflat)
      (Stacks.SheafOfModules.KFlatResolution.kFlat_colimit_of_isStrictlyLE_of_isFlat_ofSize Y.O D
        hLE hDflat) α hqis (HomologicalComplex.epi_of_epi_f α hepi)
  exact kFlat_pullbackComplex_of_shortExact f (ShortComplex.kernelSequence α) hS hflatK
    (kFlat_pullbackComplex_of_acyclic f _ hMacyc hMkflat hMflat)
    (kFlat_pullbackComplex_of_isColimit f D (colimit.cocone D) (colimit.isColimit D) hLE hDflat)

/-! ### Stacks 0G7E on the unbounded homotopy category -/

/-- **Stacks 0G7E for an arbitrary morphism of ringed topoi, on the homotopy category.**
Degreewise pullback along `f` carries the class of K-flat complexes of `O`-modules with flat
terms into the same class for `O'`.

Nothing happens on passage to the homotopy category: the underlying complex of `K(f^*)K` is `f^*`
of the underlying complex of `K`.  The K-flatness clause is `kFlat_pullbackComplex` and the
flat-terms clause is `isFlat_pullbackComplex_X`, i.e. Stacks 05VD alone. -/
@[stacks 0G7E "K-flat with flat terms is preserved, for an arbitrary morphism of ringed topoi"]
theorem isKFlat_pullbackMapHomotopy (f : RingedToposHom X Y)
    (K : HomotopyCategory (SheafOfModules.{w'} (SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))
    (hK : Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat (Y := Y) K) :
    Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat (Y := X)
      ((Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy f).obj K) := by
  refine ⟨?_, fun i ↦ isFlat_pullbackComplex_X f K.as hK.2 i⟩
  exact (Stacks.SheafOfModules.KFlat.kFlat_iff_kFlatBifunctor X.O _).1
    (kFlat_pullbackComplex f K.as
      ((Stacks.SheafOfModules.KFlat.kFlat_iff_kFlatBifunctor Y.O K.as).2 hK.1) hK.2)

end Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom

end

end
