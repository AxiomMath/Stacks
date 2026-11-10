module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.SheafInternalHomFirstVariable
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomRestriction
public import StacksFrontier.AlgebraicGeometry.Reflexive.Basic
public import StacksFrontier.AlgebraicGeometry.ReflexiveHull.CoherentDual

/-!
# The first assertion of Stacks 01CQ at `𝒢 = 𝒪_X`

Let `X` be a scheme and let `F` be an `𝒪_X`-module of finite presentation.  Then every point of
`X` has an open neighbourhood `U` on which the dual `F^∨ = SheafHom(F, 𝒪_X)` is the kernel of a
morphism between two finite direct sums of copies of `𝒪_U`.  This is the first assertion of
[Stacks, Tag 01CQ](https://stacks.math.columbia.edu/tag/01CQ) at `𝒢 = 𝒪_X`, and it is the one
input that the reflexive-hull theory of
[Stacks, Tag 0EBH](https://stacks.math.columbia.edu/tag/0EBH) and the reflexivity clause of
[Stacks, Tag 0EBF](https://stacks.math.columbia.edu/tag/0EBF) need beyond their own hypotheses.

The proof is the Stacks Project's.  Finite presentation gives, on each member `U` of an open
cover, an exact sequence `𝒪_U^{⊕ m} ⟶ 𝒪_U^{⊕ n} ⟶ F|_U ⟶ 0`; that is Mathlib's
`SheafOfModules.QuasicoherentData` together with `SheafOfModules.Presentation.isColimit`.
Applying `SheafHom(-, 𝒪_U)` turns the cokernel into a kernel, because the internal Hom is left
exact in its first variable, and turns `𝒪_U^{⊕ k}` into `𝒪_U^{⊕ k}`, because it turns a
coproduct into a product — which for a finite index is again a direct sum — and because the dual
of `𝒪_U` is `𝒪_U`.  Those three facts are `ihomCokernelIsoKernel`, `ihomCoproductIsoProduct` and
`ihomUnitIso` of
`StacksFrontier/Algebra/Category/ModuleCat/Presheaf/SheafInternalHomFirstVariable.lean`.

Neither integrality nor local Noetherianity is used: the statement holds for an arbitrary
scheme, and no coherence hypothesis replaces the finite presentation of `F`.

## Main definitions

* `HasLocalKernelPresentationDual X`: the first assertion of Tag 01CQ at `𝒢 = 𝒪_X`, as a
  predicate on `X`.  The 0EBH- and 0EBF-shaped statements of
  `StacksFrontier/AlgebraicGeometry/ReflexiveHull/CoherentDual.lean` rest on it; the theorem below
  supplies it for every scheme.
* `schemeRingedSite`: a scheme read as a ringed site, the shape in which the internal-Hom
  development of Chapter 18, Section 27 states its results.
* `dualSheafOverIso` and `dualSheafOverIhomIso`: **the restriction of the dual is the dual of
  the restriction**, `F^∨|_U ≅ (F|_U)^∨`, the second form reading the right-hand side as the
  internal hom of the monoidal closed structure on `𝒪_U`-modules.

## Main results

* `hasLocalKernelPresentationDual`: **the first assertion of Tag 01CQ at `𝒢 = 𝒪_X`**, for an
  arbitrary scheme.

## Implementation notes

The local presentation of `F` lives on the slice site `Opens(X)/U`, not on `Opens U`, because
that is where Mathlib's `QuasicoherentData` puts it; so the whole computation is carried out in
the category of modules over `𝒪_X|_U` on that slice, and no open subscheme is formed.  The one
step that has to cross between `U` and `X` is therefore the identification of `F^∨|_U` with the
dual of `F|_U` computed on the slice, which is Tag 0E8H, already in the tree as
`Stacks.SheafOfModules.InternalHom.internalHomOverIso`; `dualSheafOverIso` is that isomorphism
of presheaves of modules promoted along the fully faithful forgetful functor.

Two spellings of the sheaf of rings of the slice are in play: `X.ringCatSheaf.over U`, which is
what `SheafOfModules.over` produces and which `HasLocalKernelPresentationDual` is stated over,
and `Stacks.SheafOfModules.Tensor.ringSheaf (X.sheaf.over U)`, which is the spelling the monoidal
structure — and hence `MonoidalClosed.ihom` — synthesizes for.  They are equal by `rfl`, both
being the structure presheaf reindexed along `Over.forget U` with commutativity forgotten, but
only the second is of the syntactic shape instance search needs; the statements below are
therefore phrased in the second and cross to the first by definitional unfolding, at the one
point where the two meet.

`HasLocalKernelPresentationDual` is stated with the finite direct sums indexed by `Fin m` and
`Fin n` and the target spelled `SheafOfModules.unit X.ringCatSheaf`, because that is the shape
`Stacks.SheafOfModules.isCoherent_of_locallyKernelFiniteCoproduct` consumes and the shape Tag
01CQ states; restating it with an arbitrary finite index type would need a reindexing at every
use.

**Why the tag of Tag 01CQ is withheld.**  That tag is stated for an arbitrary ringed space and an
arbitrary target `𝒢`, and it has two assertions.  The second — "in particular, if `𝒢` is
coherent then `SheafHom(F, 𝒢)` is coherent too" — is in the tree, for an arbitrary site, as
`Stacks.SheafOfModules.isCoherent_of_locallyKernelFiniteCoproduct`.  The first is proved here
only at `𝒢 = 𝒪_X` and only over a scheme, which is all the reflexive-hull theory needs.  The
inputs it is assembled from (`ihomCokernelIsoKernel`, `ihomCoproductIsoProduct` and
`ihomUnitIso`) are stated for an arbitrary target and an arbitrary site, so the general
statement is within reach of the same three lemmas plus Tag 0E8H's `internalHomOverIso`, which
is already stated for a ringed site; the tag belongs on that statement together with
`isCoherent_of_locallyKernelFiniteCoproduct`, not here.

## References

* [Stacks Project, Tag 01CQ](https://stacks.math.columbia.edu/tag/01CQ)
* [Stacks Project, Tag 0E8H](https://stacks.math.columbia.edu/tag/0E8H)
* [Stacks Project, Tag 03EN](https://stacks.math.columbia.edu/tag/03EN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite TopologicalSpace
open AlgebraicGeometry Stacks.SheafOfModules.InternalHom

noncomputable section

universe u

namespace Stacks.AlgebraicGeometry.ReflexiveModules

/-! ### The predicate

`HasLocalKernelPresentationDual` — the first assertion of Stacks 01CQ at `𝒢 = 𝒪_X`, that the
dual of a finitely presented module is locally the kernel of a map between finite direct sums of
copies of the structure sheaf — is defined once, in
`StacksFrontier.AlgebraicGeometry.ReflexiveHull.CoherentDual`, and imported here.
`hasLocalKernelPresentationDual` below carries out the proof.
-/

/-- **A scheme as a ringed site**: the site of its opens with the structure sheaf.  This is the
shape in which the internal-Hom development of Chapter 18, Section 27 states its results. -/
public def schemeRingedSite (X : Scheme.{u}) : RingedSite.{u, u, u} where
  C := Opens ↥X
  J := Opens.grothendieckTopology ↥X
  O := X.sheaf

/-- **The restriction of the dual is the dual of the restriction**, `F^∨|_U ≅ (F|_U)^∨`, where
the right-hand side is the internal Hom of Tag 03EM computed on the slice site over `U`.

This is Tag 0E8H, `internalHomOverIso`, transported from presheaves of modules to sheaves of
modules along the fully faithful forgetful functor. -/
public def dualSheafOverIso (X : Scheme.{u}) (U : X.Opens) (F : X.Modules) :
    (dualSheaf F).over U ≅
      (internalHomSecondFunctor ((Opens.grothendieckTopology ↥X).over U)
        (X.sheaf.over U) (F.over U)).obj (SheafOfModules.unit (X.ringCatSheaf.over U)) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (internalHomOverIso (schemeRingedSite X) U F (SheafOfModules.unit X.ringCatSheaf))

section

attribute [local instance] _root_.SheafOfModules.monoidalCategory
  _root_.SheafOfModules.symmetricCategory SheafOfModules.monoidalClosed

/-- Modules on the slice site have finite biproducts: they are preadditive and have finite
products.  Mathlib does not make this an instance, and the finite direct sums of Tag 01CQ need
it. -/
instance hasFiniteBiproductsOver (X : Scheme.{u}) (U : X.Opens) :
    HasFiniteBiproducts
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.sheaf.over U))) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- **The structure sheaf of the slice site over `U`**, spelled as the restriction `(𝒪_X)|_U`
that `HasLocalKernelPresentationDual` states its direct sums in, but typed as a module over the
slice's own structure sheaf `𝒪_{X|_U}`, which is the spelling instance search needs.  The two
sheaves of rings are the same by definitional unfolding; an `abbrev` keeps the term on the
`HasLocalKernelPresentationDual` side of that unfolding while the category stays on the other,
so that no coproduct ever has to be compared across it. -/
public abbrev sliceUnit (X : Scheme.{u}) (U : X.Opens) :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.sheaf.over U)) :=
  (SheafOfModules.unit X.ringCatSheaf).over U

/-- **The dual on the slice site over `U`**, `SheafHom(-, 𝒪_U)`, read as the internal hom of the
monoidal closed structure on `𝒪_U`-modules.  An `abbrev` so that it unifies with the underlying
`MonoidalClosed.internalHom` without a transport. -/
public abbrev sliceDual (X : Scheme.{u}) (U : X.Opens) :
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.sheaf.over U)))ᵒᵖ ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.sheaf.over U)) :=
  MonoidalClosed.internalHom.flip.obj (SheafOfModules.unit _)

/-- **The restriction of the dual, as the internal hom of the monoidal closed structure.**  This
is `dualSheafOverIso` followed by the internal-Hom bridge `ihomIsoInternalHom`, which is what
makes the first-variable continuity of
`StacksFrontier/Algebra/Category/ModuleCat/Presheaf/SheafInternalHomFirstVariable.lean` apply to the
dual. -/
public def dualSheafOverIhomIso (X : Scheme.{u}) (U : X.Opens) (F : X.Modules) :
    (dualSheaf F).over U ≅ (sliceDual X U).obj (op (F.over U)) :=
  dualSheafOverIso X U F ≪≫
    (ihomIsoInternalHom (X.sheaf.over U) (F.over U)
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (X.sheaf.over U)))).symm

/-- **The dual of a finite free module on the slice site is a finite direct sum of copies of
`𝒪_U`.**  The dual of the coproduct is the product of the duals, each dual of `𝒪_U` is `𝒪_U`,
and a finite product is a finite direct sum.

The direct sum is produced in the spelling `(𝒪_X)|_U` that `HasLocalKernelPresentationDual`
states it in, rather than in the spelling `𝒪_{X|_U}` that the monoidal structure synthesizes
for: the two are the same sheaf of modules by definitional unfolding, and crossing between them
at this one isomorphism of structure sheaves is cheap, whereas crossing inside a coproduct is
not. -/
public def sliceDualFreeIsoSigma (X : Scheme.{u}) (U : X.Opens) {ι : Type u} {k : ℕ}
    (e : ι ≃ Fin k) :
    (sliceDual X U).obj (op (SheafOfModules.free (R := X.ringCatSheaf.over U) ι)) ≅
      ∐ fun _ : Fin k => sliceUnit X U :=
  ihomCoproductIsoProduct (X.sheaf.over U)
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (X.sheaf.over U)))
      (fun _ : ι => SheafOfModules.unit (X.ringCatSheaf.over U)) ≪≫
    Pi.whiskerEquiv (g := fun _ : Fin k => sliceUnit X U) e
      (fun _ => (ihomUnitIso (X.sheaf.over U)
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (X.sheaf.over U)))).symm) ≪≫
    (biproduct.isoProduct _).symm ≪≫ biproduct.isoCoproduct _

/-- **The first assertion of Stacks, Tag 01CQ, at `𝒢 = 𝒪_X`**, for an arbitrary scheme: the dual
of a module of finite presentation is, around every point, the kernel of a morphism between two
finite direct sums of copies of the structure sheaf.

Finite presentation supplies a cover on whose members `F` is the cokernel of a morphism between
two finite free modules, which is `SheafOfModules.Presentation.isColimit`; dualizing turns that
cokernel into a kernel, by `ihomCokernelIsoKernel`, and the two finite free modules into finite
direct sums of copies of `𝒪_U` again, by `sliceDualFreeIsoSigma`.

The tag of Tag 01CQ is withheld: that tag is stated over a ringed space for an arbitrary target
`𝒢` and has a second assertion besides this one.  See the implementation notes. -/
public theorem hasLocalKernelPresentationDual (X : Scheme.{u}) :
    HasLocalKernelPresentationDual X := by
  intro F hF x
  obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData F
  obtain ⟨i, hxU⟩ := ((Opens.coversTop_iff _ q.X).1 q.coversTop).exists_mem x
  have hPfin : (q.presentation i).IsFinite := hq.isFinite_presentation i
  obtain ⟨n, ⟨eg⟩⟩ := Finite.exists_equiv_fin (q.presentation i).generators.I
  obtain ⟨m, ⟨er⟩⟩ := Finite.exists_equiv_fin (q.presentation i).relations.I
  have isoG := sliceDualFreeIsoSigma X (q.X i) eg
  have isoR := sliceDualFreeIsoSigma X (q.X i) er
  obtain ⟨dg, ⟨hker⟩⟩ :
      ∃ dg : (sliceDual X (q.X i)).obj
            (op (SheafOfModules.free (R := X.ringCatSheaf.over (q.X i))
              (q.presentation i).generators.I)) ⟶
          (sliceDual X (q.X i)).obj
            (op (SheafOfModules.free (R := X.ringCatSheaf.over (q.X i))
              (q.presentation i).relations.I)),
        Nonempty ((dualSheaf F).over (q.X i) ≅ kernel dg) :=
    ⟨_, ⟨dualSheafOverIhomIso X (q.X i) F ≪≫
      ihomCokernelIsoKernel (X.sheaf.over (q.X i)) _ (q.presentation i).isColimit⟩⟩
  exact ⟨q.X i, hxU, n, m, isoG.inv ≫ dg ≫ isoR.hom,
    ⟨hker ≪≫ kernel.mapIso dg _ isoG isoR
      (Iso.hom_inv_id_assoc isoG (dg ≫ isoR.hom)).symm⟩⟩

end

end Stacks.AlgebraicGeometry.ReflexiveModules

end

end
