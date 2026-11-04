module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfSheafFlatBaseChangeProved
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.HigherDirectImageSmoothLocalCriterion

/-!
# Locally quasi-coherent modules with the flat base change property: the fppf sheaf condition
and the higher direct images

**Stacks 0771** collects what the category `LQCoh^fbc(𝒪_𝒳)` of locally quasi-coherent
`𝒪_𝒳`-modules with the flat base change property satisfies. Its parts are

1. a member of `LQCoh^fbc(𝒪_𝒳)`, a condition on a module on the *étale* site, is already a sheaf
   for the *fppf* topology, hence is an object of `Mod(𝒪_𝒳)`;
2. `LQCoh^fbc(𝒪_𝒳)` is a weak Serre subcategory of `Mod(𝒪_𝒳)` and of `Mod(𝒳_étale, 𝒪_𝒳)`;
3. the inverse image along a 1-morphism carries `LQCoh^fbc(𝒪_𝒴)` into `LQCoh^fbc(𝒪_𝒳)`;
4. for `f` quasi-compact and quasi-separated, (a) `Rf_*ℱ` and the `Rⁱf_*ℱ` do not depend on
   whether they are computed on the étale or on the fppf site, and (b) each `Rⁱf_*ℱ` lies again
   in `LQCoh^fbc(𝒪_𝒴)`.

This file delivers part (1) and part (4)(b). Part (3) is already carried, in its local
quasi-coherence half, by
`AlgebraicGeometry.Stack.isLocallyQuasicoherentWithFlatBaseChange_stackModulePresheafPullback`.
Parts (2) and (4)(a) are not here; what each of them needs is set out in the implementation
notes.

## Main definitions

* `AlgebraicGeometry.Stack.fppfModuleOfLocallyQuasicoherentWithFlatBaseChange`: the object of
  `Mod(𝒪_𝒳)` which a member of `LQCoh^fbc(𝒪_𝒳)` is, by part (1).

## Main results

* `AlgebraicGeometry.Stack.isSheaf_fppf_of_isLocallyQuasicoherentWithFlatBaseChange`:
  **Stacks 0771 part (1)**, the fppf sheaf condition.
* `AlgebraicGeometry.Stack.fppfModuleOfLocallyQuasicoherentWithFlatBaseChange_mem`: the object
  part (1) produces lies in the subcategory `LQCoh^fbc(𝒪_𝒳) ⊆ Mod(𝒪_𝒳)` whose derived category
  **Stacks 07B6** takes the Verdier quotient of.
* `AlgebraicGeometry.Stack.isLocallyQuasicoherentWithFlatBaseChangeUnivLE_`
  `moduleSheafHigherDirectImage`: **Stacks 0771 part (4)(b)**, in the étale reading and in every
  degree.

## Implementation notes

### Part (1), and what it carries

The source proves part (1) by citing **Stacks 076T**: a locally quasi-coherent module whose
comparison map `c_φ` of **Stacks 06WC** is an isomorphism along every arrow lying over a flat
morphism *locally of finite presentation* is an fppf sheaf. Membership in `LQCoh^fbc` asks that
isomorphism along every arrow lying over a flat morphism, finitely presented or not, so it
implies the hypothesis of **Stacks 076T** by
`AlgebraicGeometry.Stack.hasFlatLfpBaseChangeProperty_of_hasFlatBaseChangeProperty`, and part (1)
is that implication followed by **Stacks 076T**.

**Stacks 076T** is reduced to one step of its own proof, the sheaf condition along a family of
arrows lying over an fppf covering of schemes
(`AlgebraicGeometry.Stack.IsSheafForLiftedFppfFamily`), in
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/FppfSheafFromFlatBaseChange.lean`, and that
step is proved in
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/FppfSheafFlatBaseChangeProved.lean`, so
part (1) carries nothing.

The statement here is for an arbitrary category fibred in groupoids over the big fppf site,
which is the generality of **Stacks 076T**; the source states part (1) for an algebraic stack,
and `AlgebraicGeometry.Stack.fppfModuleOfLocallyQuasicoherentWithFlatBaseChange` is the
specialization that produces the object of `Mod(𝒪_𝒳)` the source's clause ends with.

### Part (4)(b), and why it is the étale reading

The conclusion of the criterion of **Stacks 076Z** at the rule `LQCoh^fbc`
(`AlgebraicGeometry.Stack.locallyQuasicoherentFlatBaseChangeRule`) is exactly part (4)(b): for a
quasi-compact quasi-separated 1-morphism, the higher direct images of
**Stacks 06WE** carry members of the rule to members of the rule. The theorem
`AlgebraicGeometry.Stack.hasFlatBaseChangePropertyUnivLE_moduleSheafHigherDirectImage`
(**Stacks 0765**) runs that criterion and then keeps only the flat base change conjunct, and
`AlgebraicGeometry.Stack.isLocallyQuasicoherent_moduleSheafHigherDirectImage` (**Stacks 075Z**)
runs it at the rule of local quasi-coherence alone. Part (4)(b) is the conjunction, and it is
obtained from the same six hypotheses **Stacks 0765** carries — the criterion itself, the weak
Serre condition for the rule, the flat base change half of smooth-local stability, the two
halves of its converse, and the affine case — with no further hypothesis. So no mathematics of
the source is added here beyond the pairing, and the honest reading of this file is that
part (4)(b) rests entirely on those six.

The rule reads the flat base change property at section universe `u + 1`, by
`AlgebraicGeometry.Stack.HasFlatBaseChangePropertyUnivLE`, because the higher direct images of
module sheaves produce modules whose sections lie there while
`AlgebraicGeometry.Stack.HasFlatBaseChangeProperty` is pinned to the universe `u` of the
schemes.

Both the hypothesis on `ℱ` and the conclusion are read on the *étale* site, which is where the
criterion of **Stacks 076Z** and the rules it is applied to live, and where the source's own
Lemma for part (4)(b) sits. The source's default topology is the fppf one, and the two readings
agree by part (4)(a); that agreement is **not** asserted here, and the tag attribute says so.

### Parts (2) and (4)(a)

Part (2) asks that `LQCoh^fbc` be a weak Serre subcategory of the étale and of the fppf modules.
It splits along the two halves of the definition of `LQCoh^fbc`. The local quasi-coherence half
is **Stacks 06WM** parts (2) and (3), proved at section universe `u` in
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/LocallyQuasicoherentWeakSerre.lean`; part (4)
of the same tag is in
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/LocallyQuasicoherentTensor.lean`. The flat
base change half is **Stacks 0764** part (2), of which
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/FlatBaseChangeColimits.lean` has the zero
object and the closure under cokernels for the presheaves of modules; the kernel clause of 0764
part (2) is the one that consumes exactness of `a_{small}^*` along a flat morphism of schemes.
The fppf half asks besides that the fppf cokernel of a map of members be the sheafification of
the étale one, and the locality of `H¹` of **Stacks 01FW** for the extension clause.

Part (4)(a) identifies the étale and the fppf higher direct images of a member. The source
deduces it from the comparison lemma **Stacks 075R** together with part (1); **Stacks 075R** has
no formalization in this library, so part (4)(a) cannot be run, and with it the reading of
part (4)(b) on the fppf site is out of reach.

## References

* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
* [Stacks Project, Tag 06WE](https://stacks.math.columbia.edu/tag/06WE)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 06WM](https://stacks.math.columbia.edu/tag/06WM)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 0764](https://stacks.math.columbia.edu/tag/0764)
* [Stacks Project, Tag 0765](https://stacks.math.columbia.edu/tag/0765)
* [Stacks Project, Tag 075R](https://stacks.math.columbia.edu/tag/075R)
* [Stacks Project, Tag 075Z](https://stacks.math.columbia.edu/tag/075Z)
* [Stacks Project, Tag 076T](https://stacks.math.columbia.edu/tag/076T)
* [Stacks Project, Tag 076Z](https://stacks.math.columbia.edu/tag/076Z)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 07B6](https://stacks.math.columbia.edu/tag/07B6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v w t s

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Part (1): a member of `LQCoh^fbc` is an fppf sheaf -/

section PartOne

variable {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)

/-- **Stacks 0771, part (1).** A presheaf of modules over the structure sheaf of a category
fibred in groupoids over the big fppf site which is locally quasi-coherent (**Stacks 06WJ**) and
has the flat base change property (**Stacks 0762**) — that is, a member of `LQCoh^fbc(𝒪_𝒳)` — is
a sheaf for the fppf topology of **Stacks 06TP**.

Membership in `LQCoh^fbc` asks the comparison map `c_φ` of **Stacks 06WC** to be an isomorphism
along every arrow lying over a flat morphism of schemes, which is more than the hypothesis of
**Stacks 076T**, where only the arrows lying over a flat morphism locally of finite presentation
are looked at. So part (1) is **Stacks 076T** after
`AlgebraicGeometry.Stack.hasFlatLfpBaseChangeProperty_of_hasFlatBaseChangeProperty`. -/
@[stacks 0771 "part (1): a member of LQCoh^fbc is a sheaf for the fppf topology of Stacks 06TP; \
  stated for every category fibred in groupoids, which generalizes the source's algebraic \
  stack"]
theorem isSheaf_fppf_of_isLocallyQuasicoherentWithFlatBaseChange
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj)
    (hF : IsLocallyQuasicoherentWithFlatBaseChange B E h S hS p hp F) :
    Presheaf.IsSheaf (associatedTopology B S hS p B.topology) F.presheaf :=
  isSheaf_fppf_of_isLocallyQuasicoherent_of_flatBaseChange B E h S hS p hp F hF.1
    (hasFlatLfpBaseChangeProperty_of_hasFlatBaseChangeProperty B E h S hS p hp
      (etaleTopology B) (etaleTopology_le_topology B) F hF.2)

end PartOne

section PartOneStack

variable (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- **Stacks 0771, part (1)**, the object of `Mod(𝒪_𝒳)` the source's clause ends with: a member
of `LQCoh^fbc(𝒪_𝒳)`, being a sheaf for the fppf topology by
`AlgebraicGeometry.Stack.isSheaf_fppf_of_isLocallyQuasicoherentWithFlatBaseChange`, is a module
on the fppf site of the algebraic stack.

No transport is involved. The presheaf of rings underlying the structure sheaf of **Stacks 06TV**
is `p.op ⋙ (BigFppfOver.structureSheaf B S hS).obj` whichever of the five topologies of
**Stacks 06TP** it is read at, so the presheaf of modules is already a presheaf of modules over
the fppf structure sheaf, and only its sheaf condition has to be improved. -/
@[stacks 0771 "part (1), the clause `hence lies in Mod(𝒪_𝒳)`: the module on the fppf site of an \
  algebraic stack that a member of LQCoh^fbc is"]
def fppfModuleOfLocallyQuasicoherentWithFlatBaseChange
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B)).obj)
    (hF : IsLocallyQuasicoherentWithFlatBaseChange B E h S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids F) :
    fppfModules B S hS 𝒳 where
  val := F
  isSheaf := isSheaf_fppf_of_isLocallyQuasicoherentWithFlatBaseChange B E h S hS
    𝒳.val.val.p 𝒳.val.isFiberedInGroupoids F hF

/-- The module on the fppf site produced by part (1) has the given presheaf of modules
underneath it: part (1) changes the sheaf condition and nothing else. -/
@[simp]
theorem fppfModuleOfLocallyQuasicoherentWithFlatBaseChange_val
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B)).obj)
    (hF : IsLocallyQuasicoherentWithFlatBaseChange B E h S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids F) :
    (fppfModuleOfLocallyQuasicoherentWithFlatBaseChange B E h S hS 𝒳 F hF).val = F :=
  rfl

/-- The module on the fppf site produced by part (1) lies in the subcategory
`LQCoh^fbc(𝒪_𝒳) ⊆ Mod(𝒪_𝒳)` whose derived category **Stacks 07B6** takes the Verdier quotient
of. Its membership condition is a condition on the underlying presheaf of modules, which part (1)
leaves alone. -/
theorem fppfModuleOfLocallyQuasicoherentWithFlatBaseChange_mem
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B)).obj)
    (hF : IsLocallyQuasicoherentWithFlatBaseChange B E h S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids F) :
    locallyQuasicoherentFlatBaseChangeFppfModules B E h S hS 𝒳
      (fppfModuleOfLocallyQuasicoherentWithFlatBaseChange B E h S hS 𝒳 F hF) :=
  hF

end PartOneStack

/-! ### Part (4)(b): the higher direct images carry `LQCoh^fbc` into `LQCoh^fbc` -/

/-- **Stacks 0771, part (4)(b).** Let `f : 𝒳 ⟶ 𝒴` be a quasi-compact (**Stacks 050U**) and
quasi-separated (**Stacks 04YW**) 1-morphism of algebraic stacks over `S` and let `ℱ` be a sheaf
of `𝒪_𝒳`-modules on `𝒳_étale` which is locally quasi-coherent (**Stacks 06WJ**) and has the flat
base change property (**Stacks 0762**). Then the higher direct image `Rⁱf_*ℱ` of **Stacks 06WE**,
computed in the étale topology, is again locally quasi-coherent *and* has the flat base change
property, in every degree `i`: that is, `Rⁱf_*` carries `LQCoh^fbc(𝒪_𝒳)` into
`LQCoh^fbc(𝒪_𝒴)`.

The flat base change property is read at section universe `u + 1`, where the higher direct images
of module sheaves live, by `AlgebraicGeometry.Stack.HasFlatBaseChangePropertyUnivLE`.

This is the conclusion of the criterion of **Stacks 076Z** at the rule `LQCoh^fbc`, so it is
obtained from exactly the six hypotheses
`AlgebraicGeometry.Stack.hasFlatBaseChangePropertyUnivLE_moduleSheafHigherDirectImage`
(**Stacks 0765**) carries, each a result of the source this library does not have: `hcrit` is
**Stacks 076Z** quantified over every rule, `hserre` is parts (1) to (3) of **Stacks 06WM** with
part (2) of **Stacks 0764**, `hfbcPull` is part (1) of **Stacks 0764**, `hconvLqc` and `hconvFbc`
are **Stacks 075Y** at section universe `u + 1` and part (3) of **Stacks 0764**, and `haffine` is
the affine case, from **Stacks 075P** and **Stacks 073K**. **Stacks 0765** is the same criterion
with only the flat base change conjunct of its conclusion kept, and **Stacks 075Z** is the
criterion at the rule of local quasi-coherence alone; neither of them states the conjunction, and
the conjunction is what part (4)(b) asserts.

Hypothesis (2) of the criterion for local quasi-coherence is **Stacks 06WL** and is not carried:
it is supplied by
`AlgebraicGeometry.Stack.isStableUnderSmoothPullback_locallyQuasicoherentRule`, which also
supplies the forward half of hypothesis (3). -/
@[stacks 0771 "part (4)(b), in every degree, over the six hypotheses Stacks 0765 carries \
  (Stacks 076Z; Stacks 06WM (1)-(3) with 0764 (2); 0764 (1) and (3); 075Y at u+1; 075P and \
  073K). THIS IS THE ETALE READING AND NOT THE TAG'S DEFAULT FPPF ONE: part (4)(a), the \
  agreement of the two, is not asserted here"]
theorem isLocallyQuasicoherentWithFlatBaseChangeUnivLE_moduleSheafHigherDirectImage
    (hcrit : SmoothLocalHigherDirectImageCriterion.{u, t, s} B S hS)
    (hserre : StackEtaleModuleRule.IsWeakSerre.{u, t} B S hS
      (locallyQuasicoherentFlatBaseChangeRule B E h S hS))
    (hfbcPull : StackEtaleModuleRule.IsStableUnderSmoothPullback.{u, t} B S hS
      (flatBaseChangePropertyRule B E h S hS))
    (hconvLqc : StackEtaleModuleRule.IsSmoothLocalConverse.{u, t, s} B S hS
      (locallyQuasicoherentRule B E h S hS))
    (hconvFbc : StackEtaleModuleRule.IsSmoothLocalConverse.{u, t, s} B S hS
      (flatBaseChangePropertyRule B E h S hS))
    (haffine : StackEtaleModuleRule.PreservesHigherDirectImagesOfAffine.{u, t} B S hS
      (locallyQuasicoherentFlatBaseChangeRule B E h S hS))
    {𝒳 𝒴 : AlgebraicStacks.{u, t} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hqc : IsQuasiCompactMorphism B S hS f)
    (hqs : AlgebraicStacks.IsQuasiSeparated B S hS f) (i : ℕ) :
    letI := hasSheafify_associatedTopology_of_category_succ B S hS
      (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
    letI := wEqualsLocallyBijective_associatedTopology_of_category_succ B S hS
      (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
    letI := hasSheafify_associatedTopology_of_category_succ B S hS 𝒴.val.val.p
    letI := wEqualsLocallyBijective_associatedTopology_of_category_succ B S hS 𝒴.val.val.p
    ∀ ℱ : SheafOfModules.{u + 1} (ringStructureSheafCore B S hS
        (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
        (isFiberedInGroupoids_homFunctor_comp B S hS f.hom)
        (etaleTopology B) (etaleTopology_le_topology B)),
      IsLocallyQuasicoherent B E h S hS
          (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
          (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) ℱ.val →
        HasFlatBaseChangePropertyUnivLE B E h S hS
            (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
            (isFiberedInGroupoids_homFunctor_comp B S hS f.hom)
            (etaleTopology B) (etaleTopology_le_topology B) ℱ.val →
          IsLocallyQuasicoherent B E h S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
              ((moduleSheafHigherDirectImage.{u, u + 1, u, u + 1, u} B S hS
                (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p) 𝒴.val.val.p
                (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) 𝒴.val.isFiberedInGroupoids
                (CatFiberedInGroupoids.homFunctor f.hom) rfl (etaleTopology B)
                (etaleTopology_le_topology B) i).obj ℱ).val ∧
            HasFlatBaseChangePropertyUnivLE B E h S hS 𝒴.val.val.p
              𝒴.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B)
              ((moduleSheafHigherDirectImage.{u, u + 1, u, u + 1, u} B S hS
                (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p) 𝒴.val.val.p
                (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) 𝒴.val.isFiberedInGroupoids
                (CatFiberedInGroupoids.homFunctor f.hom) rfl (etaleTopology B)
                (etaleTopology_le_topology B) i).obj ℱ).val :=
  fun ℱ hlqc hfbc =>
    hcrit (locallyQuasicoherentFlatBaseChangeRule B E h S hS) hserre
      (isStableUnderSmoothPullback_locallyQuasicoherentFlatBaseChangeRule B E h S hS hfbcPull)
      (isSmoothLocal_locallyQuasicoherentFlatBaseChangeRule B E h S hS hfbcPull hconvLqc
        hconvFbc)
      haffine f hqc hqs i ℱ ⟨hlqc, hfbc⟩

end AlgebraicGeometry.Stack

end
