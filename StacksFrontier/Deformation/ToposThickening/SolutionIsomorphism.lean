module

public import StacksFrontier.Deformation.ToposThickening.ExtensionProblem
public import StacksFrontier.Deformation.ToposThickening.LiftingBetweenThickenings
import StacksCore.Tactic.StacksAttribute

/-!
# A morphism of solutions of a deformation problem of ringed topoi is invertible

Fix a square-zero extension problem `S : RingedToposExtensionProblem X B` of ringed topoi, the
problem (91.13.0.1) of [Stacks Project, Tag 08UF]. A *solution* is a
`Deformation.ToposThickening.RingedToposExtensionProblem.CompatibleFirstOrderThickening S`: a
sheaf of rings `O'` on the site of `X` with a locally surjective reduction `O' ⟶ O` whose kernel
is identified with the prescribed module `G`, together with the map from the inverse image of the
thickened base and the compatibility with the prescribed map `c` on ideals.

This file introduces a *morphism* of solutions — the same data as
`CompatibleFirstOrderThickening.Iso` except that the comparison of the thickened structure
sheaves is only a morphism, not an isomorphism — and proves that such a morphism is
*automatically* invertible. This is the source's parenthetical in the proof of
[Stacks Project, Tag 08UK]: "clearly, this element is the obstruction to the existence of an
isomorphism, hence separates the isomorphism classes". The obstruction class of
[Stacks Project, Tag 08UG] obstructs a *morphism* `O'₁ ⟶ O'₂` fitting into the diagram, and the
content needed to turn that into a statement about isomorphism classes is exactly that every
such morphism is invertible.

The proof is the short five lemma on the two ideal rows, carried out section by section because
in a topos the reductions are only *locally* surjective. Two solutions `P`, `Q` sit in
sequences of sheaves of abelian groups

    0 ⟶ G ⟶ O'_P ⟶ O ⟶ 0        and        0 ⟶ G ⟶ O'_Q ⟶ O ⟶ 0

with the *same* outer terms, exact on sections on the left and in the middle and locally
surjective on the right, and a morphism of solutions is compatible with both. Hence the
comparison of the middle terms is injective on sections and locally surjective, so it is
locally bijective, so it is an isomorphism of sheaves
(`CategoryTheory.Sheaf.isLocallyBijective_iff_isIso`).

## Main definitions

* `Deformation.ToposThickening.RingedToposExtensionProblem.CompatibleFirstOrderThickening.incl`:
  the section of the thickened structure sheaf attached to a section of `G`, with its
  section-wise algebra (`incl_zero`, `incl_injective`, `exists_incl`).
* `Deformation.ToposThickening.RingedToposExtensionProblem.CompatibleFirstOrderThickening.Hom`:
  a morphism of solutions over the fixed diagram.

## Main results

* `...CompatibleFirstOrderThickening.Hom.injective_app`: a morphism of solutions is injective
  on sections.
* `...CompatibleFirstOrderThickening.Hom.isLocallySurjective`: a morphism of solutions is
  locally surjective.
* `...CompatibleFirstOrderThickening.Hom.isIso`: **a morphism of solutions is an isomorphism**.
* `...RingedToposExtensionProblem.isomorphic_iff_nonempty_hom`: **Stacks 08UK**, the half
  asserting that the obstruction separates the isomorphism classes — two solutions of the
  problem of Tag 08UF are isomorphic exactly when there is a morphism of solutions between
  them.
* `...RingedToposExtensionProblem.isomorphismClasses_mk_eq_iff`: **Stacks 08UK**, the same
  statement for the quotient `CompatibleFirstOrderThickening.IsomorphismClasses` itself.
* `Deformation.ToposThickening.LiftDiagram.Lift.isIso`: the same five-lemma comparison in the
  vocabulary of the diagram of Tag 08UG — a lift whose two comparison maps `g` and `ν` are
  bijective on sections is an isomorphism.
* `Deformation.ToposThickening.LiftDiagram.liftingObstruction_eq_zero_iff_exists_isIso_lift`:
  **Stacks 08UK**, the same half in that vocabulary — the class of Step 1 of the proof of
  Tag 08UG vanishes exactly when an *isomorphism* fits into the diagram.

## Implementation notes

**The torsor half of Tag 08UK is not claimed here**, and the tag attribute carries a clause
string saying so. The tag has two halves: that the set of isomorphism classes of solutions is
principal homogeneous under `Ext¹_O(NL_{O/O_B}, G)`, and that the obstruction class of
Tag 08UG separates those classes. Only the second is proved here. The first needs, for a
solution `O'` and a class `ξ`, the solution `O'_ξ` of the source's last paragraph, built as the
pushout of `0 ⟶ G ⟶ O' ⟶ O ⟶ 0` along `ψ = φ|_{ℐ'} + δ ∘ (ℐ' ⟶ ℐ/ℐ²)`, together with the
source's "a calculation (omitted)" identifying `o(O', O'_ξ)` with `ξ`. The pushout itself is
available on an arbitrary site as `Stacks.Sites.SqZeroPushout.pushoutSheaf`, but the presentation
`f^{-1}O_{B'}[ℰ] ↠ O'` it must be applied to is *pair-dependent*: the source obtains `α` from
Tag 08UJ for the class `ξ` and then replaces `ℰ` by `ℰ ×_O O'`, so `ℐ`, `ℐ/ℐ²` and the
difference map all depend on the chosen solution, not only on the problem `S`. In particular the
obstruction class is attached to a *presentation*, and a single fixed presentation does not
serve all pairs; the ringed-space twin
`StacksFrontier/Deformation/RingedSpaceThickening/SolutionTorsor.lean` carries that datum as a
hypothesis for the same reason. Nothing in this file depends on any of it: no obstruction class,
no pushout and no `Ext` group occurs below.

Two further things are missing before the torsor half could be assembled even with a
pair-dependent presentation, and both are recorded here because they are what the difference
class `o(O'₁, O'₂)` would be built from. First, the difference cocycle of two solutions is
produced by `Stacks.Sites.Conormal.conormalDifference` as a map out of `ℐ'/(ℐ')²`, the conormal
sheaf of the presentation with the *thickened* coefficients, whereas the conormal term of
`NL(α)` — the group Tag 08UK needs — is `ℐ/ℐ²`; the surjection `ℐ' ↠ ℐ` with kernel
`𝒥 · f^{-1}O_{B'}[ℰ]` along which the source descends it is not in the library, only the map
`Stacks.Sites.Conormal.presentationConormalMap` running the other way. Second, clause (1) of
Tag 08UG is formalized as the vanishing criterion
`Deformation.ToposThickening.LiftDiagram.liftingObstruction_eq_zero_iff` for the factorizations
of a *given* conormal homomorphism, so the library does not yet produce the `Ext¹` class of a
*pair* of solutions at all — it consumes one. Until it does there is no difference map to make
the isomorphism classes a torsor under, which is why what is proved here is exactly the
separation statement.

**Why the argument is section-wise rather than an application of the five lemma in an abelian
category.** The analogous ringed-space statement
`AlgebraicGeometry.RingedSpaceThickening.SolutionHom.isIso_structureMap` runs the short five
lemma in `ShortComplex` form in the abelian category of sheaves of modules, using that the
reduction of a first order thickening of ringed spaces is an epimorphism. Here the reduction is
only locally surjective, so the right-hand map of the ideal row is not an epimorphism of
presheaves and the rows are not short exact as complexes of presheaves. The replacement is
`CategoryTheory.Sheaf.isLocallyBijective_iff_isIso`: injectivity on sections of the comparison
comes from the two *section-wise* kernel identifications
`CompatibleFirstOrderThickening.kernelUniversal`, and local surjectivity is produced by
refining a local lift of the reduction and correcting it by a section of `G`, which is where the
surjectivity half of `kernelUniversal` on the target is used.

**Instances.** `CategoryTheory.Sheaf.isLocallyBijective_iff_isIso` for sheaves of commutative
rings needs `X.J.HasSheafCompose (forget CommRingCat)`, which is not among the instance
arguments that `RingedToposExtensionProblem` itself carries, so it is added as an instance
argument here; the same for `(forget CommRingCat).ReflectsIsomorphisms`.

## References

* [Stacks Project, Tag 08UK](https://stacks.math.columbia.edu/tag/08UK)
* [Stacks Project, Tag 08UF](https://stacks.math.columbia.edu/tag/08UF)
* [Stacks Project, Tag 08UG](https://stacks.math.columbia.edu/tag/08UG)
* [Stacks Project, Tag 08UC](https://stacks.math.columbia.edu/tag/08UC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)

universe v u w v' u' w'

/-- If `ρ (f a) = ρ b` and every element killed by `ρ` is some `f (ι m)`, then `b = f a'`. -/
private theorem exists_eq_of_reduction_eq {A B R M : Type*} [Ring A] [Ring B] [Ring R]
    (f : A →+* B) (ρ : B →+* R) (ι : M → A) (hex : ∀ x, ρ x = 0 → ∃ m, f (ι m) = x)
    {a : A} {b : B} (h : ρ (f a) = ρ b) : ∃ a', f a' = b := by
  obtain ⟨m, hm⟩ := hex (f a - b) (by rw [map_sub, h, sub_self])
  exact ⟨a - ι m, by rw [map_sub, hm, sub_sub_cancel]⟩

namespace Deformation.ToposThickening.RingedToposExtensionProblem

variable {X : RingedTopos.{v, u, w}}
  {B : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [B.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  {S : RingedToposExtensionProblem X B}

namespace CompatibleFirstOrderThickening

/-! ### The ideal of a solution, section by section -/

/-- The section of the thickened structure sheaf of a solution attached to a section of the
prescribed module `G`, through the chosen kernel identification. -/
public noncomputable def incl (P : S.CompatibleFirstOrderThickening) {U : X.Cᵒᵖ}
    (g : S.G.val.obj U) : P.extension.obj.obj U :=
  P.kernelInclusion.val.app U g

/-- The inclusion of the prescribed module is additive on sections. -/
public theorem incl_add (P : S.CompatibleFirstOrderThickening) {U : X.Cᵒᵖ}
    (g h : S.G.val.obj U) : P.incl (g + h) = P.incl g + P.incl h :=
  map_add (P.kernelInclusion.val.app U).hom g h

/-- The inclusion of the prescribed module sends `0` to `0`. -/
public theorem incl_zero (P : S.CompatibleFirstOrderThickening) {U : X.Cᵒᵖ} :
    P.incl (0 : S.G.val.obj U) = 0 :=
  map_zero (P.kernelInclusion.val.app U).hom

/-- The reduction of a solution kills the image of the prescribed module. -/
public theorem reduction_incl (P : S.CompatibleFirstOrderThickening) {U : X.Cᵒᵖ}
    (g : S.G.val.obj U) : P.reduction.hom.app U (P.incl g) = 0 :=
  P.kernelZero U g

/-- The inclusion of the prescribed module is injective on sections: this is the uniqueness
half of `CompatibleFirstOrderThickening.kernelUniversal`. -/
public theorem incl_injective (P : S.CompatibleFirstOrderThickening) {U : X.Cᵒᵖ} :
    Function.Injective (P.incl (U := U)) := by
  intro g h hgh
  obtain ⟨p, -, hp⟩ := P.kernelUniversal U (P.incl g) (P.kernelZero U g)
  exact (hp g rfl).trans (hp h hgh.symm).symm

/-- A section of the thickened structure sheaf killed by the reduction comes from the
prescribed module: this is the existence half of
`CompatibleFirstOrderThickening.kernelUniversal`. -/
public theorem exists_incl (P : S.CompatibleFirstOrderThickening) {U : X.Cᵒᵖ}
    (a : P.extension.obj.obj U) (ha : P.reduction.hom.app U a = 0) :
    ∃ g : S.G.val.obj U, P.incl g = a := by
  obtain ⟨g, hg, -⟩ := P.kernelUniversal U a ha
  exact ⟨g, hg⟩

/-- Scalars act on the ideal of a solution through the reduction: the product of a section of the
thickened structure sheaf with a section of the ideal is the image of the action of its
reduction.

Both scalars are read in `(sheafCompose X.J (forget₂ CommRingCat RingCat)).obj _`, the spelling
of the underlying sheaf of rings that `S.G` and `kernelInclusion` are indexed by. The reduced
section is spelled out rather than passed through
`Deformation.ToposThickening.toRingSection`, whose value is read in
`Stacks.SheafOfModules.Tensor.ringSheaf X.O`: that is the same sheaf of rings, but a
spelling that instance search cannot reduce to the one carried by `S.G`. -/
public theorem mul_incl (P : S.CompatibleFirstOrderThickening) {U : X.Cᵒᵖ}
    (a : P.extension.obj.obj U) (g : S.G.val.obj U) :
    a * P.incl g =
      P.incl ((show ↥(((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj
        X.O).obj.obj U) from P.reduction.hom.app U a) • g) :=
  (map_smul (P.kernelInclusion.val.app U).hom
    (show ↥(((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj
      P.extension).obj.obj U) from a)
    (show ((SheafOfModules.restrictScalars
      ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).map P.reduction)).obj
        S.G).val.obj U from g)).symm

/-- The inclusion of the prescribed module commutes with the restriction maps of the site. -/
public theorem incl_naturality (P : S.CompatibleFirstOrderThickening) {U V : X.Cᵒᵖ} (h : U ⟶ V)
    (g : S.G.val.obj U) :
    P.incl (show S.G.val.obj V from S.G.val.map h g) = P.extension.obj.map h (P.incl g) :=
  PresheafOfModules.naturality_apply P.kernelInclusion.val h g

/-! ### Morphisms of solutions -/

/-- A morphism of solutions of the extension problem of [Stacks Project, Tag 08UF]: a morphism
of the thickened structure sheaves which is over the reduced structure sheaf, under the inverse
image of the thickened base, and the identity on the prescribed module `G`.

This is the data of `CompatibleFirstOrderThickening.Iso` with the comparison of the thickened
structure sheaves weakened from an isomorphism to a morphism; `Hom.isIso` says the weakening
is only apparent. -/
public structure Hom (P Q : S.CompatibleFirstOrderThickening) where
  /-- The morphism of the thickened structure sheaves. -/
  hom : P.extension ⟶ Q.extension
  /-- It is over the reduced structure sheaf. -/
  reduction_comm : hom ≫ Q.reduction = P.reduction
  /-- It respects the map from the inverse image of the thickened base. -/
  baseMap_comm : P.baseMap ≫ hom = Q.baseMap
  /-- It is the identity on the prescribed module `G`. -/
  kernel_comm : ∀ (U : X.Cᵒᵖ) (g : S.G.val.obj U),
    hom.hom.app U (P.incl g) = Q.incl g

namespace Hom

variable {P Q : S.CompatibleFirstOrderThickening}

/-- The reduction of the image of a section under a morphism of solutions is the reduction of
that section. -/
public theorem reduction_apply (e : Hom P Q) {U : X.Cᵒᵖ} (a : P.extension.obj.obj U) :
    Q.reduction.hom.app U (e.hom.hom.app U a) = P.reduction.hom.app U a :=
  congrArg (fun k : P.extension ⟶ X.O => k.hom.app U a) e.reduction_comm

/-- **A morphism of solutions is injective on sections.** A section killed by it is killed by
the reduction of the source, hence comes from `G`; its image is then its own inclusion into the
target, which is injective, so the section of `G` vanishes. -/
public theorem injective_app (e : Hom P Q) (U : X.Cᵒᵖ) :
    Function.Injective (e.hom.hom.app U) :=
  (injective_iff_map_eq_zero (e.hom.hom.app U).hom).2 fun a ha => by
    obtain ⟨g, rfl⟩ := P.exists_incl a (by rw [← e.reduction_apply a]; simp [ha])
    rw [e.kernel_comm, ← Q.incl_zero] at ha
    rw [Q.incl_injective ha, P.incl_zero]

/-- **A morphism of solutions is locally surjective.** A section `b` of the target reduces to a
section of `O`, which lifts locally through the locally surjective reduction of the source; the
difference between the image of such a local lift and `b` is killed by the reduction of the
target, hence is the inclusion of a section `g` of `G`, and subtracting the inclusion of `g` in
the source corrects the lift exactly. -/
public theorem isLocallySurjective (e : Hom P Q) :
    Presheaf.IsLocallySurjective X.J e.hom.hom where
  imageSieve_mem {U} b := by
    refine X.J.superset_covering ?_
      (P.locallySurjective.imageSieve_mem (Q.reduction.hom.app (op U) b))
    rintro V f ⟨a, ha⟩
    exact exists_eq_of_reduction_eq (e.hom.hom.app (op V)).hom (Q.reduction.hom.app (op V)).hom
      P.incl (fun x hx => (Q.exists_incl x hx).imp fun g hg => (e.kernel_comm _ g).trans hg)
      ((e.reduction_apply a).trans
        (ha.trans (NatTrans.naturality_apply Q.reduction.hom f.op b).symm))

variable [X.J.HasSheafCompose (forget CommRingCat.{w})]
  [(forget CommRingCat.{w}).ReflectsIsomorphisms]

/-- **A morphism of solutions is an isomorphism.** It is injective on sections, hence locally
injective, and locally surjective, and a locally bijective morphism of sheaves is an
isomorphism. -/
public theorem isIso (e : Hom P Q) : IsIso e.hom :=
  (Sheaf.isLocallyBijective_iff_isIso e.hom).1
    ⟨(Sheaf.isLocallyInjective_iff_injective e.hom).2 e.injective_app, e.isLocallySurjective⟩

/-- A morphism of solutions, read as an isomorphism of solutions. -/
public noncomputable def toIso (e : Hom P Q) : Iso P Q where
  hom := @asIso _ _ _ _ e.hom e.isIso
  reduction_comm := e.reduction_comm
  baseMap_comm := e.baseMap_comm
  kernel_comm := e.kernel_comm

end Hom

/-- The identity morphism of a solution; in particular the notion of a morphism of solutions is
not vacuous. -/
public def Hom.id (P : S.CompatibleFirstOrderThickening) : Hom P P where
  hom := 𝟙 P.extension
  reduction_comm := Category.id_comp _
  baseMap_comm := Category.comp_id _
  kernel_comm _ _ := rfl

/-- The underlying morphism of an isomorphism of solutions. -/
public def Iso.toHom {P Q : S.CompatibleFirstOrderThickening} (e : Iso P Q) : Hom P Q where
  hom := e.hom.hom
  reduction_comm := e.reduction_comm
  baseMap_comm := e.baseMap_comm
  kernel_comm := e.kernel_comm

end CompatibleFirstOrderThickening

variable [X.J.HasSheafCompose (forget CommRingCat.{w})]
  [(forget CommRingCat.{w}).ReflectsIsomorphisms]

/-- **Stacks Project, Tag 08UK**, the half asserting that the obstruction class separates the
isomorphism classes of solutions. Two solutions of the square-zero extension problem of
[Stacks Project, Tag 08UF] are isomorphic exactly when there is a *morphism* of solutions
between them: by `CompatibleFirstOrderThickening.Hom.isIso` every morphism of solutions is
already invertible.

This is the source's "clearly, this element is the obstruction to the existence of an
isomorphism, hence separates the isomorphism classes" — the obstruction class of
[Stacks Project, Tag 08UG], which obstructs a morphism `O'₁ ⟶ O'₂` fitting into the diagram
(`Deformation.ToposThickening.LiftDiagram.liftingObstruction_eq_zero_iff`), thereby obstructs an
isomorphism of solutions.

The other half of the tag — that the isomorphism classes form a principal homogeneous space
under `Ext¹_O(NL_{O/O_B}, G)` — is **not** claimed here; see the implementation notes of this
file. -/
@[stacks 08UK "the half asserting that the obstruction class of Stacks 08UG separates the \
isomorphism classes of solutions, namely that a morphism of solutions of the extension problem \
of Stacks 08UF is automatically an isomorphism; not the torsor half, which needs the \
pair-dependent presentation of the source's last paragraph and its omitted calculation"]
public theorem isomorphic_iff_nonempty_hom (P Q : S.CompatibleFirstOrderThickening) :
    CompatibleFirstOrderThickening.Isomorphic P Q ↔
      Nonempty (CompatibleFirstOrderThickening.Hom P Q) :=
  ⟨fun h => h.elim fun e => ⟨e.toHom⟩, fun h => h.elim fun e => ⟨e.toIso⟩⟩

/-- **Stacks Project, Tag 08UK**, the half asserting that the obstruction class separates the
isomorphism classes, stated for the set of isomorphism classes itself. Two solutions of the
square-zero extension problem of [Stacks Project, Tag 08UF] have the same class in
`CompatibleFirstOrderThickening.IsomorphismClasses S` exactly when there is a morphism of
solutions between them, so the obstruction class of [Stacks Project, Tag 08UG] — which
obstructs such a morphism — is a complete invariant of the isomorphism class.

That these classes are moreover *principal homogeneous* under
`Ext¹_O(NL_{O/O_B}, G)` is **not** claimed; see the implementation notes of this file. -/
@[stacks 08UK "the half asserting that the obstruction class of Stacks 08UG separates the \
isomorphism classes, stated for the quotient `IsomorphismClasses` itself: two solutions have \
the same isomorphism class exactly when a morphism of solutions joins them; not the torsor \
half"]
public theorem isomorphismClasses_mk_eq_iff (P Q : S.CompatibleFirstOrderThickening) :
    (Quotient.mk (CompatibleFirstOrderThickening.isomorphicSetoid S) P :
        CompatibleFirstOrderThickening.IsomorphismClasses S) =
      Quotient.mk (CompatibleFirstOrderThickening.isomorphicSetoid S) Q ↔
      Nonempty (CompatibleFirstOrderThickening.Hom P Q) :=
  Quotient.eq.trans (isomorphic_iff_nonempty_hom P Q)

end Deformation.ToposThickening.RingedToposExtensionProblem

/-! ### The same statement in the vocabulary of the diagram of Stacks 08UG -/

namespace Deformation.ToposThickening

universe u₂ v₂ u₃ v₃

namespace LiftDiagram

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] {D : LiftDiagram J}

namespace Lift

/-- **A lift whose two comparison maps are bijective is injective on sections.** A section
killed by the lift is killed by the comparison of the reduced structure sheaves composed with
the reduction of the front layer, hence — the comparison being injective — by that reduction
alone, so it comes from the front ideal `G₁`; its image is the inclusion of its comparison in
`G₂`, which vanishes, so the section of `G₁` vanishes too. -/
public theorem injective_app (p : Lift D)
    (hg : ∀ U : Cᵒᵖ, Function.Injective (D.g.hom.app U))
    (hnu : ∀ U : Cᵒᵖ, Function.Injective (D.nuSection (U := U))) (U : Cᵒᵖ) :
    Function.Injective (p.hom.hom.app U) :=
  (injective_iff_map_eq_zero (p.hom.hom.app U).hom).2 fun a ha => by
    obtain ⟨m, rfl⟩ := D.front.exists_incl a (hg U (by rw [← p.reduction_apply a]; simp [ha]))
    rw [p.kernel_comm, ← D.back.incl_zero] at ha
    rw [hnu U ((D.back.incl_injective ha).trans (map_zero (D.nu.val.app U).hom).symm),
      D.front.incl_zero]

/-- **A lift whose two comparison maps are surjective is locally surjective.** A section `b` of
the back thickened structure sheaf reduces to a section of `O₂`, which lifts locally through
the locally surjective composite `O'₁ ⟶ O₁ ⟶ O₂`; the difference between the image of such a
local lift and `b` is killed by the back reduction, hence is the inclusion of a section of
`G₂`, which is the comparison of a section of `G₁`, and subtracting its inclusion in the front
layer corrects the lift exactly. -/
public theorem isLocallySurjective (p : Lift D)
    (hgs : Presheaf.IsLocallySurjective J D.g.hom)
    (hnus : ∀ U : Cᵒᵖ, Function.Surjective (D.nuSection (U := U))) :
    Presheaf.IsLocallySurjective J p.hom.hom where
  imageSieve_mem {U} b := by
    have hfs : Presheaf.IsLocallySurjective J D.front.reduction.hom :=
      D.front.locallySurjective
    have hcomp : Presheaf.IsLocallySurjective J (D.front.reduction.hom ≫ D.g.hom) :=
      Presheaf.isLocallySurjective_comp J _ _
    refine J.superset_covering ?_
      (hcomp.imageSieve_mem (D.back.reduction.hom.app (op U) b))
    rintro V f ⟨a, ha⟩
    rw [NatTrans.comp_app, ConcreteCategory.comp_apply] at ha
    refine exists_eq_of_reduction_eq (p.hom.hom.app (op V)).hom
      (D.back.reduction.hom.app (op V)).hom D.front.incl fun x hx => by
        obtain ⟨n, rfl⟩ := D.back.exists_incl x hx
        obtain ⟨m, rfl⟩ := hnus (op V) n
        exact ⟨m, p.kernel_comm _ m⟩
      ((p.reduction_apply a).trans
        (ha.trans (NatTrans.naturality_apply D.back.reduction.hom f.op b).symm))

variable [J.HasSheafCompose (forget CommRingCat.{w})]
  [(forget CommRingCat.{w}).ReflectsIsomorphisms]

/-- **A lift whose two comparison maps are bijective on sections is an isomorphism.** It is
injective on sections, hence locally injective, and locally surjective, and a locally bijective
morphism of sheaves is an isomorphism. -/
public theorem isIso (p : Lift D)
    (hg : ∀ U : Cᵒᵖ, Function.Bijective (D.g.hom.app U))
    (hgs : Presheaf.IsLocallySurjective J D.g.hom)
    (hnu : ∀ U : Cᵒᵖ, Function.Bijective (D.nuSection (U := U))) : IsIso p.hom :=
  (Sheaf.isLocallyBijective_iff_isIso p.hom).1
    ⟨(Sheaf.isLocallyInjective_iff_injective p.hom).2
        (p.injective_app (fun U => (hg U).1) fun U => (hnu U).1),
      p.isLocallySurjective hgs fun U => (hnu U).2⟩

end Lift

section NaiveCotangent

open AlgebraicGeometry.RingedSpaceThickening

variable {M : Type u₂} [Category.{v₂} M] [Abelian M] {T : Type u₃} [Category.{v₃} T]
  [HasZeroObject T] [HasShift T ℤ] [Preadditive T] [∀ n : ℤ, (shiftFunctor T n).Additive]
  [Pretriangulated T] [J.HasSheafCompose (forget CommRingCat.{w})]
  [(forget CommRingCat.{w}).ReflectsIsomorphisms]

/-- **Stacks Project, Tag 08UK**, the half asserting that the obstruction class separates the
isomorphism classes, in the vocabulary of the diagram of [Stacks Project, Tag 08UG]. When the
two comparison maps of the diagram are bijective on sections — as they are for two solutions of
one square-zero extension problem, where both are identities — the class of Step 1 of the proof
of Tag 08UG vanishes if and only if there is an *isomorphism* `O'₁ ≅ O'₂` fitting into the
diagram, and not merely a morphism.

This is the source's "clearly, this element is the obstruction to the existence of an
isomorphism, hence separates the isomorphism classes", combined with the vanishing criterion
`Deformation.ToposThickening.LiftDiagram.liftingObstruction_eq_zero_iff` of Tag 08UG, whose
hypotheses `P` and `ξ` are inherited verbatim. That criterion is stated for the factorizations
of `ξ` through the degree `0` term and assumes nothing; the bijection `e` of Steps 1 to 3 of the
source's proof, which identifies those factorizations with the lifts of the diagram, is carried
here. -/
@[stacks 08UK "the half asserting that the obstruction class of Stacks 08UG separates the \
isomorphism classes, stated in the vocabulary of the diagram of that tag: when the two \
comparison maps of the diagram are bijective on sections the class vanishes exactly when an \
isomorphism fits into the diagram; the hypotheses carried are those of Stacks 08UG itself, and \
the torsor half of 08UK is not claimed"]
public theorem liftingObstruction_eq_zero_iff_exists_isIso_lift (D : LiftDiagram J)
    {single : M ⥤ T} [single.Full] [single.Faithful] [single.Additive]
    (hg : ∀ U : Cᵒᵖ, Function.Bijective (D.g.hom.app U))
    (hgs : Presheaf.IsLocallySurjective J D.g.hom)
    (hnu : ∀ U : Cᵒᵖ, Function.Bijective (D.nuSection (U := U)))
    (P : NaiveCotangentTwoTerm single) (G : M) (ξ : P.conormal ⟶ G)
    (e : D.Lift ≃ {θ : P.base ⟶ G // P.d ≫ θ = ξ}) :
    liftingObstruction P G ξ = 0 ↔ ∃ p : D.Lift, IsIso p.hom := by
  have h : liftingObstruction P G ξ = 0 ↔ Nonempty D.Lift :=
    (LiftDiagram.liftingObstruction_eq_zero_iff P G ξ).trans e.nonempty_congr.symm
  rw [h]
  exact ⟨fun h => h.elim fun p => ⟨p, p.isIso hg hgs hnu⟩, fun h => h.elim fun p _ => ⟨p⟩⟩

end NaiveCotangent

end LiftDiagram

end Deformation.ToposThickening

end
