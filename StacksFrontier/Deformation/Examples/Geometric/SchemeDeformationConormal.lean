module

public import Mathlib.RingTheory.DualNumber
public import Mathlib.RingTheory.KrullDimension.Zero
public import StacksFrontier.AlgebraicGeometry.Bridge.SchemeBridge
public import StacksFrontier.AlgebraicGeometry.Conormal.SquareFlatIso
public import StacksFrontier.Deformation.Examples.Geometric.OpenSubschemes
public import StacksFrontier.Deformation.VersalObject.MinimalVersalOrbitBijection
public import StacksFrontier.Topology.Sheaves.Functors.Module.ExactSupportSections
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackUnit
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The conormal sheaf of the special fibre of a first-order deformation

Let `X` be a scheme over a field `k` and let `P` be a deformation of `X` over an object `A` of
`𝒞_Λ`, in the sense of [Stacks Project, Tag 0DY7]: a flat scheme `X'` over `Spec A` together
with a cartesian square identifying its fibre over the closed point of `Spec A` with `X`.

Because the structure morphism `X' ⟶ Spec A` is flat, the conormal sheaf of the special-fibre
closed immersion `X ⟶ X'` is the pullback along `X ⟶ Spec k` of the conormal sheaf of the
closed point `Spec k ⟶ Spec A`; this is flat base change for conormal sheaves,
[Stacks Project, Tag 0473]. When `A` is the dual numbers `k[ε]`, that latter conormal sheaf is
the structure sheaf of `Spec k`, because the maximal ideal of `k[ε]` is the square-zero
principal ideal `(ε)` and is therefore free of rank one over the residue field. Combining the
two, and using that the pullback of a structure sheaf is a structure sheaf, the conormal sheaf
of the special fibre of a first-order deformation is the structure sheaf of `X`.

## Main definitions

* `Deformation.Examples.deformationConormalBaseChangeIso`: flat base change for the conormal
  sheaf of the special fibre, `p_X^* 𝒞_{Spec k / Spec A} ≅ 𝒞_{X/X'}`.
* `Deformation.Examples.idealSheafIsoOfKerIsoTop`,
  `Deformation.Examples.conormalIsoOfIdealSheafIso`,
  `Deformation.Examples.residueConormalIso` and `Deformation.Examples.deformationConormalIso`:
  the computation with no hypothesis on the base object beyond its being an object of `𝒞_Λ` — the
  ideal sheaf of the closed point is whatever sheaf has the kernel of the surjection on global
  sections as its global sections, the conormal sheaf is the coefficient sheaf whose pushforward
  that ideal sheaf is, and the conormal sheaf of the special fibre is its pullback. These are
  what each of the three rank-one definitions below is an instance of.
* `Deformation.Examples.residueConormalIsoUnit`: the conormal sheaf of the closed point of the
  spectrum of an object of `𝒞_Λ` carrying a dual-number coordinate is the structure sheaf of
  `Spec k`.
* `Deformation.Examples.deformationConormalIsoUnit`: the payoff, that the conormal sheaf of the
  special fibre of a first-order deformation is the structure sheaf of `X`.
* `Deformation.Examples.dualNumbersResidueConormalIsoUnit` and
  `Deformation.Examples.dualNumbersDeformationConormalIsoUnit`: the previous two at the
  dual-number object of `𝒞_Λ` itself, with the coordinate hypothesis discharged.
* `Deformation.Examples.moduleIsoOfTop`: two sheaves of modules on a one-point space with
  isomorphic modules of global sections are isomorphic.
* `Deformation.Examples.quotientEquivDualNumberKernel`: the kernel of a surjection out of a ring
  with a dual-number coordinate, cut out by the vanishing of the first coordinate, is the target,
  by multiplication by `ε`.

## Main results

* `Deformation.Examples.artinianDualNumbersCoordinate`: the dual-number object
  `Deformation.artinianDualNumbers Λ k` of `𝒞_Λ` carries a dual-number coordinate, so the
  hypothesis of the definitions above is satisfied by the object it is meant for.
* `Deformation.Examples.subsingleton_baseSpec`: the spectrum of an object of `𝒞_Λ` is a single
  point, which is what makes the ideal sheaf on it readable off its global sections.
* `Deformation.Examples.residueSpecMap_app_eq_zero_iff`: the two descriptions of the maximal
  ideal of an object of `𝒞_Λ` with a dual-number coordinate agree, namely the kernel of the
  residue map and the vanishing of the first coordinate.

## Implementation notes

The hypothesis carried by `Deformation.Examples.residueConormalIsoUnit` and
`Deformation.Examples.deformationConormalIsoUnit` is an algebra isomorphism
`A ≃ₐ[Λ] DualNumber k` rather than an equality of objects of `𝒞_Λ`: transporting a sheaf of
modules along an equality of base objects is avoided throughout the library, and the
isomorphism is what the proof actually consumes — only the ring structure of `A` enters, through
the two descriptions of its maximal ideal. It is discharged for the intended object by
`Deformation.Examples.artinianDualNumbersCoordinate`.

The rank of the maximal ideal of `A` enters at exactly one step, and the chain is arranged so
that this is visible. `Deformation.Examples.idealSheafIsoOfKerIsoTop`,
`Deformation.Examples.conormalIsoOfIdealSheafIso`, `Deformation.Examples.residueConormalIso` and
`Deformation.Examples.deformationConormalIso` carry no rank hypothesis: they take the
identification of the kernel of the surjection on global sections as a hypothesis and propagate
it to the conormal sheaf of the special fibre. The rank-one input is
`Deformation.Examples.quotientEquivDualNumberKernel`, which identifies that kernel with the
residue field by multiplication by `ε`. For a base whose maximal ideal is square-zero of rank
`n`, what the chain needs in its place is a sheaf of modules on `Spec k` free of rank `n`
together with an identification of its global sections with that maximal ideal, read over the
global sections of `baseSpec A`; everything downstream of that identification is already stated
without a rank hypothesis.

The conormal sheaf is computed on the base, not on the total space: the only input about `A` is
`Deformation.Examples.residueConormalIsoUnit`, and the deformation enters only through flat base
change. The computation on the base is a computation of global sections, legitimate because the
spectrum of an Artinian local ring is a one-point space: a morphism of sheaves of modules on a
subsingleton space is determined by its value at `⊤`, which is
`Deformation.Examples.moduleIsoOfTop`. At `⊤` the ideal sheaf of the closed point is the kernel
of the surjection `A ⟶ k`, i.e. the maximal ideal, and
`Deformation.Examples.quotientEquivDualNumberKernel` identifies that kernel with `k` as an
`A`-module by multiplication by `ε`, square-zeroness of `(ε)` being exactly what makes
multiplication by `ε` factor through the residue field.

Passing from the ideal sheaf to the conormal sheaf is the counit of `i^* ⊣ i_*`, invertible for
a closed quotient morphism of ringed spaces; `Deformation.Examples.closedQuotientOfClosedPoint`
packages the closed point as such a morphism, its local surjectivity being surjectivity at `⊤`
again because the space is a single point.

Two spellings of the conormal sheaf of an immersion occur. The flat base change of
[Stacks Project, Tag 0473] is stated for `Stacks.Thickenings.immersionConormalSheaf`, which goes
through the canonical factorization over the coborder of [Stacks Project, Tag 01R2], while the
global-sections computation is natural for the factorization-free
`Stacks.Thickenings.schemeConormalSheaf`. `Stacks.Immersion.conormalSheafSelfIso` is the bridge,
and is applied once, in `Deformation.Examples.residueConormalIsoUnit`.

## References

* [Stacks Project, Tag 0DY7](https://stacks.math.columbia.edu/tag/0DY7)
* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2)
* [Stacks Project, Tag 0473](https://stacks.math.columbia.edu/tag/0473)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open RingedSpaceModuleAdjunction

universe u

namespace Deformation.Examples

attribute [local instance] residueSpecMap_isClosedImmersion
  deformationSpecialMap_isClosedImmersion

/-! ### Sheaves of modules on a one-point space -/

section PointModules

universe v

/-- Sections over the empty open of a sheaf of modules are a single element: the sheaf
condition over the empty cover makes that object terminal. -/
theorem moduleSections_empty_subsingleton {X : TopCat.{u}}
    {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}} (M : SheafOfModules.{max u v} R) :
    Subsingleton (M.val.obj (op ⊥)) := by
  let T : TopCat.Sheaf AddCommGrpCat.{max u v} X := ⟨M.val.presheaf, M.isSheaf⟩
  exact AddCommGrpCat.isZero_iff_subsingleton.mp
    (IsZero.of_iso (isZero_zero AddCommGrpCat)
      ((isZero_zero AddCommGrpCat).isTerminal.uniqueUpToIso T.isTerminalOfEmpty).symm)

/-- A map of modules of global sections extends to a morphism of sheaves of modules on a
one-point space: the only opens are `⊥` and `⊤`, and the sections over `⊥` are terminal. -/
def moduleHomOfTop {X : TopCat.{u}} [Subsingleton X]
    {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}} {M N : SheafOfModules.{max u v} R}
    (f : M.val.obj (op ⊤) ⟶ N.val.obj (op ⊤)) : M ⟶ N := by
  classical
  refine ⟨{ app := fun U ↦ if h : U = op ⊤ then h.symm ▸ f else 0
            naturality := ?_ }⟩
  intro U V g
  by_cases hV : V.unop = ⊤
  · have hU : U.unop = ⊤ := top_unique (hV ▸ leOfHom g.unop)
    obtain rfl : U = op ⊤ := unop_injective hU
    obtain rfl : V = op ⊤ := unop_injective hV
    have hg : g = 𝟙 (op ⊤) := Subsingleton.elim _ _
    subst g
    ext x
    simp
    rfl
  · have hbot : V.unop = ⊥ := V.unop.eq_bot_or_top.resolve_right hV
    have : Subsingleton (N.val.obj V) := by
      have h : V = op ⊥ := unop_injective hbot
      subst V
      exact moduleSections_empty_subsingleton N
    ext x
    exact @Subsingleton.elim (N.val.obj V) this _ _

/-- `Deformation.Examples.moduleHomOfTop` is the given map on global sections. -/
theorem moduleHomOfTop_apply {X : TopCat.{u}} [Subsingleton X]
    {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}} {M N : SheafOfModules.{max u v} R}
    (f : M.val.obj (op ⊤) ⟶ N.val.obj (op ⊤)) :
    (moduleHomOfTop f).val.app (op ⊤) = f := by
  simp [moduleHomOfTop]

/-- A morphism of sheaves of modules on a one-point space is determined by its value on global
sections. -/
theorem moduleHom_ext_top {X : TopCat.{u}} [Subsingleton X]
    {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}} {M N : SheafOfModules.{max u v} R}
    {f g : M ⟶ N} (h : f.val.app (op ⊤) = g.val.app (op ⊤)) : f = g := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  rcases U.unop.eq_bot_or_top with hU | hU
  · obtain rfl : U = op ⊥ := unop_injective hU
    have := moduleSections_empty_subsingleton N
    ext x
    exact Subsingleton.elim _ _
  · obtain rfl : U = op ⊤ := unop_injective hU
    exact h

/-- **Two sheaves of modules on a one-point space with isomorphic global sections are
isomorphic.** -/
def moduleIsoOfTop {X : TopCat.{u}} [Subsingleton X]
    {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}} {M N : SheafOfModules.{max u v} R}
    (f : M.val.obj (op ⊤) ≅ N.val.obj (op ⊤)) : M ≅ N where
  hom := moduleHomOfTop f.hom
  inv := moduleHomOfTop f.inv
  hom_inv_id := moduleHom_ext_top (by
    change (moduleHomOfTop f.hom).val.app (op ⊤) ≫
      (moduleHomOfTop f.inv).val.app (op ⊤) = 𝟙 _
    rw [moduleHomOfTop_apply, moduleHomOfTop_apply, f.hom_inv_id])
  inv_hom_id := moduleHom_ext_top (by
    change (moduleHomOfTop f.inv).val.app (op ⊤) ≫
      (moduleHomOfTop f.hom).val.app (op ⊤) = 𝟙 _
    rw [moduleHomOfTop_apply, moduleHomOfTop_apply, f.inv_hom_id])

end PointModules

/-! ### The kernel of a surjection with square-zero principal kernel -/

/-- **The kernel of a surjection whose kernel is the square-zero principal ideal `(ε)` is the
quotient, as a module over the source.** The identification carries the class of `a` to `ε * a`;
it is well defined because `ε` annihilates the kernel, and surjective because the kernel is
generated by `ε`. -/
@[sga "7 VIII 2.1.14" "special case"]
def quotientEquivPrincipalKernel
    {R S : Type*} [CommRing R] [CommRing S]
    (q : R →+* S) (ε : R) (hq : Function.Surjective q)
    (hε : q ε = 0)
    (hexact : ∀ x, q x = 0 ↔ ∃ a, ε * a = x)
    (hann : ∀ a, ε * a = 0 ↔ q a = 0) :
    letI := q.toAlgebra
    {E : S ≃ₗ[R] RingHom.ker q // ∀ a, (E (q a)).val = ε * a} := by
  letI := q.toAlgebra
  let qL : R →ₗ[R] S := Algebra.linearMap R S
  let m : R →ₗ[R] RingHom.ker q :=
    { toFun := fun a ↦ ⟨ε * a, by simp [RingHom.mem_ker, hε]⟩
      map_add' := fun _ _ ↦ Subtype.ext (mul_add _ _ _)
      map_smul' := fun _ _ ↦ Subtype.ext (mul_left_comm _ _ _) }
  have hm : Function.Surjective m := fun x ↦
    ((hexact x.val).mp x.property).imp fun _ ha ↦ Subtype.ext ha
  have hqL : Function.Surjective qL := hq
  have hk : LinearMap.ker qL = LinearMap.ker m := by
    ext a
    change q a = 0 ↔ m a = 0
    rw [← hann a]
    exact ⟨fun h ↦ Subtype.ext h, fun h ↦ congrArg Subtype.val h⟩
  let E := (qL.quotKerEquivOfSurjective hqL).symm.trans
    ((Submodule.quotEquivOfEq _ _ hk).trans (m.quotKerEquivOfSurjective hm))
  refine ⟨E, fun a ↦ ?_⟩
  change (((m.quotKerEquivOfSurjective hm)
    ((Submodule.quotEquivOfEq _ _ hk)
      ((qL.quotKerEquivOfSurjective hqL).symm (qL a))))).val = _
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

/-- **The kernel of a surjection out of a ring with a dual-number coordinate, for which the
kernel is the vanishing of the first coordinate, is the target.** The principal generator is
`ε` read through the coordinate, and `(ε) = (ε)²·0` makes
`Deformation.Examples.quotientEquivPrincipalKernel` apply. -/
def quotientEquivDualNumberKernel
    {R S k : Type*} [CommRing R] [CommRing S] [Field k]
    (q : R →+* S) (c : R ≃+* DualNumber k) (hq : Function.Surjective q)
    (hker : ∀ x, q x = 0 ↔ (c x).fst = 0) :
    letI := q.toAlgebra
    {E : S ≃ₗ[R] RingHom.ker q //
      ∀ a, (E (q a)).val = c.symm DualNumber.eps * a} := by
  apply quotientEquivPrincipalKernel q (c.symm DualNumber.eps) hq
  · rw [hker]
    simp
  · intro x
    rw [hker, DualNumber.fst_eq_zero_iff_eps_dvd]
    exact ⟨fun ⟨a, ha⟩ ↦ ⟨c.symm a, c.injective (by simpa using ha.symm)⟩,
      fun ⟨a, ha⟩ ↦ ⟨c a, by simpa using (congrArg c ha).symm⟩⟩
  · intro a
    rw [hker, ← c.map_eq_zero_iff]
    simp only [map_mul, c.apply_symm_apply]
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · simpa only [DualNumber.eps, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_inr,
        TrivSqZeroExt.snd_inr, zero_smul, zero_add, MulOpposite.smul_eq_mul_unop,
        MulOpposite.unop_op, one_mul, TrivSqZeroExt.snd_zero] using congrArg TrivSqZeroExt.snd h
    · ext <;> simp only [DualNumber.eps, TrivSqZeroExt.fst_mul,
        TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr,
        zero_smul, zero_add, h, TrivSqZeroExt.fst_zero, TrivSqZeroExt.snd_zero, zero_mul,
        MulOpposite.op_zero]

/-! ### The ideal sheaf and the conormal sheaf of a point with a dual-number coordinate -/

/-- **The ideal sheaf of a closed point of a one-point space is whatever sheaf of modules has the
kernel of the surjection on global sections as its global sections.** On a one-point space a
sheaf of modules is determined by its module of global sections
(`Deformation.Examples.moduleIsoOfTop`), and the global sections of the ideal sheaf are the
kernel of the surjection on global sections: evaluation at `⊤` commutes with the kernel because
it preserves zero morphisms, and the kernel of a map of modules is its `LinearMap.ker`.

**No rank hypothesis enters**, and no hypothesis on the ring of global sections of `Y` at all:
the kernel is identified with the target sheaf by the hypothesis `E`. The rank-one case, where
the kernel is the square-zero principal ideal `(ε)` and the target sheaf is the pushforward of
the structure sheaf, is `Deformation.Examples.idealSheafIsoPushforwardUnitOfCoordinate`; a base
whose maximal ideal has rank `n` needs an `E` landing in a sheaf whose global sections are that
maximal ideal. -/
def idealSheafIsoOfKerIsoTop
    {X Y : RingedSpace.{u, u}} [Subsingleton Y] (t : X ⟶ Y)
    (M : SheafOfModules.{u} (structureSheafRing Y))
    (E : ModuleCat.of (Y.presheaf.obj (op ⊤))
          (RingHom.ker ((structureSheafHom t).hom.app (op ⊤)).hom) ≅
        (SheafOfModules.evaluation (structureSheafRing Y) (op ⊤)).obj M) :
    Stacks.ClosedImmersion.idealSheaf t ≅ M := by
  let f := SheafOfModules.unitToPushforwardObjUnit (structureSheafHom t)
  let F := SheafOfModules.evaluation (structureSheafRing Y) (op ⊤)
  letI : F.PreservesZeroMorphisms := ⟨fun _ _ ↦ rfl⟩
  let κ : F.obj (kernel f) ≅ kernel (F.map f) := asIso (kernelComparison f F)
  exact moduleIsoOfTop (κ ≪≫ ModuleCat.kernelIsoKer (F.map f) ≪≫ E)

/-- **The ideal sheaf of a closed point of a one-point space with a dual-number coordinate is
the pushforward of the structure sheaf.** This is
`Deformation.Examples.idealSheafIsoOfKerIsoTop` with its identification of the kernel supplied by
`Deformation.Examples.quotientEquivDualNumberKernel`, which identifies the kernel with the target
of the surjection by multiplication by `ε` — the one step of the computation that uses the base
being of rank one. -/
def idealSheafIsoPushforwardUnitOfCoordinate
    {X Y : RingedSpace.{u, u}} [Subsingleton Y] (t : X ⟶ Y)
    {k : Type u} [Field k]
    (c : Y.presheaf.obj (op ⊤) ≃+* DualNumber k)
    (hq : Function.Surjective ((structureSheafHom t).hom.app (op ⊤)).hom)
    (hker : ∀ x, ((structureSheafHom t).hom.app (op ⊤)).hom x = 0 ↔ (c x).fst = 0) :
    Stacks.ClosedImmersion.idealSheaf t ≅
      (modulePushforward t).obj (SheafOfModules.unit (structureSheafRing X)) :=
  let q : Y.presheaf.obj (op ⊤) →+* X.presheaf.obj (op ((opensMap t).obj ⊤)) :=
    (t.hom.c.app (op ⊤)).hom
  letI := q.toAlgebra
  idealSheafIsoOfKerIsoTop t _
    (quotientEquivDualNumberKernel q c hq hker).val.symm.toModuleIso

/-- A morphism of ringed spaces out of a one-point space which is a closed embedding and
surjective on global sections is a closed quotient morphism: local surjectivity of the
comorphism is surjectivity at `⊤`, because `⊤` is the only nonempty open. -/
def closedQuotientOfTopSurjective
    {X Y : RingedSpace.{u, u}} [Subsingleton Y] (t : X ⟶ Y)
    (hclosed : Topology.IsClosedEmbedding t.hom.base)
    (hq : Function.Surjective (t.hom.c.app (op ⊤)).hom) :
    ClosedQuotientMorphismOfRingedSpaces where
  X := Y
  Z := X
  i := t
  isClosedEmbedding := hclosed
  isLocallySurjective := by
    apply (TopCat.Presheaf.isLocallySurjective_iff _).2
    intro U s y hy
    obtain rfl : U = ⊤ := by
      ext z
      exact ⟨fun _ ↦ trivial, fun _ ↦ (Subsingleton.elim (α := Y) y z) ▸ hy⟩
    obtain ⟨a, ha⟩ := hq s
    refine ⟨⊤, le_rfl, ⟨a, ?_⟩, trivial⟩
    change (t.hom.c.app (op ⊤)).hom a =
      (((TopCat.Presheaf.pushforward CommRingCat t.hom.base).obj X.presheaf).map
        (𝟙 (op ⊤))).hom s
    exact ha.trans (congrArg (fun f : X.presheaf.obj (op ⊤) ⟶ _ ↦ f.hom s)
      (((TopCat.Presheaf.pushforward CommRingCat t.hom.base).obj X.presheaf).map_id
        (op ⊤))).symm

/-- For a closed quotient morphism of ringed spaces, pullback undoes pushforward: the counit of
`i^* ⊣ i_*` is invertible. -/
def closedQuotientPullbackPushforwardIso
    (S : ClosedQuotientMorphismOfRingedSpaces.{u})
    (M : SheafOfModules (structureSheafRing S.Z)) :
    (modulePullback S.i).obj ((modulePushforward S.i).obj M) ≅ M :=
  asIso ((modulePullbackPushforwardAdjunction S.i).counit.app M)

/-- **The conormal sheaf of a closed point of a one-point scheme is the coefficient sheaf whose
pushforward is the ideal sheaf.** Pulling the ideal sheaf back undoes the pushforward, by
`Deformation.Examples.closedQuotientPullbackPushforwardIso`.

**No rank hypothesis enters**: the coefficient sheaf `N` is arbitrary, and which one it is is
decided by the hypothesis `E` on the ideal sheaf — for a base whose maximal ideal has rank one
by `Deformation.Examples.idealSheafIsoPushforwardUnitOfCoordinate`, with `N` the structure
sheaf, and for rank `n` by an ideal-sheaf identification with the pushforward of a sheaf free of
rank `n`. -/
def conormalIsoOfIdealSheafIso
    {X Y : Scheme.{u}} [Subsingleton Y] (t : X ⟶ Y) [IsClosedImmersion t]
    (hq : Function.Surjective (t.app ⊤).hom)
    {N : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)}
    (E : Stacks.ClosedImmersion.idealSheaf t.toLRSHom.toShHom ≅
      (modulePushforward t.toLRSHom.toShHom).obj N) :
    Stacks.Thickenings.schemeConormalSheaf t ≅ N :=
  let S := closedQuotientOfTopSurjective t.toLRSHom.toShHom t.isClosedEmbedding hq
  (modulePullback t.toLRSHom.toShHom).mapIso E ≪≫
    closedQuotientPullbackPushforwardIso S N

/-- **The conormal sheaf of a closed point of a one-point scheme with a dual-number coordinate
is the structure sheaf.** This is `Deformation.Examples.conormalIsoOfIdealSheafIso` at the
coefficient sheaf `𝒪_X`, its ideal-sheaf hypothesis discharged by
`Deformation.Examples.idealSheafIsoPushforwardUnitOfCoordinate`. -/
def conormalIsoUnitOfCoordinate
    {X Y : Scheme.{u}} [Subsingleton Y] (t : X ⟶ Y) [IsClosedImmersion t]
    {k : Type u} [Field k]
    (c : Y.presheaf.obj (op ⊤) ≃+* DualNumber k)
    (hq : Function.Surjective (t.app ⊤).hom)
    (hker : ∀ x, (t.app ⊤).hom x = 0 ↔ (c x).fst = 0) :
    Stacks.Thickenings.schemeConormalSheaf t ≅
      SheafOfModules.unit (structureSheafRing X.toRingedSpace) :=
  conormalIsoOfIdealSheafIso t hq
    (idealSheafIsoPushforwardUnitOfCoordinate t.toLRSHom.toShHom c hq hker)

/-! ### The conormal sheaf of the closed point of the spectrum of an object of `𝒞_Λ` -/

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The spectrum of an object of `𝒞_Λ` is a single point: an Artinian local ring has exactly
one prime ideal. -/
instance subsingleton_baseSpec (A : ArtinianLocalAlgCat.{u, u, u} Λ k) :
    Subsingleton (baseSpec A) :=
  Ring.KrullDimLE.subsingleton_primeSpectrum A

/-- The dual-number coordinate of an object of `𝒞_Λ`, read on the global sections of its
spectrum. -/
def baseSpecCoordinate {A : ArtinianLocalAlgCat.{u, u, u} Λ k}
    (coordinate : A ≃ₐ[Λ] DualNumber k) :
    (baseSpec A).presheaf.obj (op ⊤) ≃+* DualNumber k :=
  (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv.trans coordinate.toRingEquiv

/-- A global function on the spectrum of an object of `𝒞_Λ` restricts to zero at the closed
point exactly when the first coordinate of its dual-number expansion vanishes: both conditions
say that the function lies in the maximal ideal. -/
theorem residueSpecMap_app_eq_zero_iff (A : ArtinianLocalAlgCat.{u, u, u} Λ k)
    (coordinate : A ≃ₐ[Λ] DualNumber k) (a : (baseSpec A).presheaf.obj (op ⊤)) :
    ((residueSpecMap A).app ⊤).hom a = 0 ↔ (baseSpecCoordinate coordinate a).fst = 0 := by
  let q : A →+* k := Deformation.Artin.residueMap A
  let r : A →+* k :=
    (TrivSqZeroExt.fstHom k k k).toRingHom.comp coordinate.toRingEquiv.toRingHom
  have hr : Function.Surjective r := fun a =>
    ⟨coordinate.symm (TrivSqZeroExt.inl a), by simp [r]⟩
  have hker : RingHom.ker q = RingHom.ker r := by
    rw [IsLocalRing.ker_eq_maximalIdeal q (residueMap_surjective A),
      IsLocalRing.ker_eq_maximalIdeal r hr]
  have hnat := congrArg (fun f : (baseSpec A).presheaf.obj (op ⊤) ⟶ CommRingCat.of k ↦ f.hom a)
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom q))
  change (Scheme.ΓSpecIso (.of k)).hom.hom (((residueSpecMap A).app ⊤).hom a) =
    q ((Scheme.ΓSpecIso (.of A)).hom.hom a) at hnat
  have hzero : ((residueSpecMap A).app ⊤).hom a = 0 ↔
      q ((Scheme.ΓSpecIso (.of A)).hom.hom a) = 0 := by
    rw [← hnat]
    exact (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.map_eq_zero_iff.symm
  rw [hzero]
  change (Scheme.ΓSpecIso (.of A)).hom.hom a ∈ RingHom.ker q ↔
    (Scheme.ΓSpecIso (.of A)).hom.hom a ∈ RingHom.ker r
  rw [hker]

/-- **The conormal sheaf of the closed point of the spectrum of an object of `𝒞_Λ` is the
coefficient sheaf on `Spec k` whose pushforward is the ideal sheaf of that point.** The
spectrum of an Artinian local ring is a single point, so
`Deformation.Examples.conormalIsoOfIdealSheafIso` applies, and the surjectivity it asks for is
the surjectivity of a closed immersion on the global sections of an affine.

**No hypothesis on the rank of the maximal ideal of `A` enters.** The rank-one case is
`Deformation.Examples.residueConormalIsoUnit`; a base whose maximal ideal has rank `n` needs an
`E` identifying the ideal sheaf with the pushforward of a sheaf on `Spec k` free of rank `n`.
Two spellings of the conormal sheaf occur and `Stacks.Immersion.conormalSheafSelfIso` is the
bridge, as in the rank-one case. -/
def residueConormalIso (A : ArtinianLocalAlgCat.{u, u, u} Λ k)
    {N : SheafOfModules.{u}
      (structureSheafRing (Spec (CommRingCat.of k)).toRingedSpace)}
    (E : Stacks.ClosedImmersion.idealSheaf (residueSpecMap A).toLRSHom.toShHom ≅
      (modulePushforward (residueSpecMap A).toLRSHom.toShHom).obj N) :
    Stacks.Thickenings.immersionConormalSheaf (residueSpecMap A) ≅ N :=
  (Stacks.Immersion.conormalSheafSelfIso (residueSpecMap A)).symm ≪≫
    conormalIsoOfIdealSheafIso (residueSpecMap A)
      ((residueSpecMap A).app_surjective ⊤ (isAffineOpen_top _)) E

/-- **The conormal sheaf of the closed point of the spectrum of an object of `𝒞_Λ` whose
maximal ideal is square-zero and one-dimensional over `k` is the structure sheaf of
`Spec k`.** The hypothesis is carried as a dual-number coordinate `A ≃ₐ[Λ] k[ε]`, which is what
makes the maximal ideal the square-zero principal ideal `(ε)`. This is
`Deformation.Examples.residueConormalIso` with its ideal-sheaf hypothesis discharged by
`Deformation.Examples.idealSheafIsoPushforwardUnitOfCoordinate`. -/
def residueConormalIsoUnit (A : ArtinianLocalAlgCat.{u, u, u} Λ k)
    (coordinate : A ≃ₐ[Λ] DualNumber k) :
    Stacks.Thickenings.immersionConormalSheaf (residueSpecMap A) ≅
      SheafOfModules.unit (structureSheafRing (Spec (CommRingCat.of k)).toRingedSpace) :=
  residueConormalIso A
    (idealSheafIsoPushforwardUnitOfCoordinate (residueSpecMap A).toLRSHom.toShHom
      (baseSpecCoordinate coordinate)
      ((residueSpecMap A).app_surjective ⊤ (isAffineOpen_top _))
      (residueSpecMap_app_eq_zero_iff A coordinate))

/-! ### The conormal sheaf of the special fibre of a deformation -/

variable {X : Over (Spec (CommRingCat.of k))}

/-- Flat base change: `pX^* 𝒞_{Spec k / Spec A} ≅ 𝒞_{X/X'}`. -/
def deformationConormalBaseChangeIso (P : SchemeDeformationCategory (Λ := Λ) (k := k) X) :
    (RingedSpaceModuleAdjunction.modulePullback X.hom.toLRSHom.toShHom).obj
        (Stacks.Thickenings.immersionConormalSheaf (residueSpecMap P.base)) ≅
      Stacks.Thickenings.immersionConormalSheaf P.specialMap :=
  letI : Flat P.toBase := P.flat
  haveI := Stacks.Immersion.isIso_immersionConormalSheafMap_of_flat P.specialMap
    (residueSpecMap P.base) X.hom P.toBase P.specialCartesian
  asIso (Stacks.Immersion.immersionConormalSheafMap P.specialMap (residueSpecMap P.base)
    X.hom P.toBase (Stacks.Immersion.toShHom_square P.specialCartesian.w))

/-- **The conormal sheaf of the special-fibre closed immersion of a deformation is the pullback
along the structure morphism of `X` of the conormal sheaf of the closed point of the base.**
Flat base change `Deformation.Examples.deformationConormalBaseChangeIso` reduces the statement to
the base, where the conormal sheaf of the closed point is read off by the hypothesis `ε`.

**No hypothesis on the rank of the maximal ideal of the base object enters**, and none on the
base object at all beyond its being an object of `𝒞_Λ`: the conormal sheaf of the special fibre
is the pullback of whatever the conormal sheaf of the closed point is. The rank of the base
enters only through `ε`, which for rank one is
`Deformation.Examples.residueConormalIsoUnit` and gives the structure sheaf of `X` after
`RingedSpaceModuleAdjunction.modulePullbackUnitIso`
(`Deformation.Examples.deformationConormalIsoUnit`), and for rank `n` would give a sheaf free of
rank `n`, the pullback of a structure sheaf being a structure sheaf. -/
def deformationConormalIso (P : SchemeDeformationCategory (Λ := Λ) (k := k) X)
    {N : SheafOfModules.{u}
      (structureSheafRing (Spec (CommRingCat.of k)).toRingedSpace)}
    (ε : Stacks.Thickenings.immersionConormalSheaf (residueSpecMap P.base) ≅ N) :
    Stacks.Thickenings.immersionConormalSheaf P.specialMap ≅
      (modulePullback X.hom.toLRSHom.toShHom).obj N :=
  (deformationConormalBaseChangeIso P).symm ≪≫
    (modulePullback X.hom.toLRSHom.toShHom).mapIso ε

/-- **The conormal sheaf of the special-fibre closed immersion of a first-order deformation is
the structure sheaf of the scheme being deformed.** This is
`Deformation.Examples.deformationConormalIso` with `ε` supplied by
`Deformation.Examples.residueConormalIsoUnit`, which computes the conormal sheaf of the closed
point of the base to be the structure sheaf of `Spec k`, followed by
`RingedSpaceModuleAdjunction.modulePullbackUnitIso`, which identifies its pullback with the
structure sheaf of `X`. -/
def deformationConormalIsoUnit (P : SchemeDeformationCategory (Λ := Λ) (k := k) X)
    (coordinate : P.base ≃ₐ[Λ] DualNumber k) :
    Stacks.Thickenings.immersionConormalSheaf P.specialMap ≅
      SheafOfModules.unit (structureSheafRing X.left.toRingedSpace) :=
  deformationConormalIso P (residueConormalIsoUnit P.base coordinate) ≪≫
    modulePullbackUnitIso X.hom.toLRSHom.toShHom

/-! ### The dual numbers -/

/-- **The dual-number object of `𝒞_Λ` carries a dual-number coordinate**, so the hypothesis of
`Deformation.Examples.residueConormalIsoUnit` and
`Deformation.Examples.deformationConormalIsoUnit` is satisfied by the object they are meant for.
`Deformation.artinianDualNumbers` is the square-zero extension of `k` by `ULift k`, which is
`k[ε]` with the `ε`-line lifted, and `Deformation.dualNumbersEquiv` undoes the lift. -/
def artinianDualNumbersCoordinate :
    Deformation.artinianDualNumbers.{u, u, u} Λ k ≃ₐ[Λ] DualNumber k :=
  Deformation.dualNumbersEquiv.{u, u, u}

/-- **The conormal sheaf of the closed point of the spectrum of the dual numbers is the
structure sheaf of `Spec k`**: `Deformation.Examples.residueConormalIsoUnit` at the
dual-number object of `𝒞_Λ`, whose coordinate is
`Deformation.Examples.artinianDualNumbersCoordinate`. -/
def dualNumbersResidueConormalIsoUnit :
    Stacks.Thickenings.immersionConormalSheaf
        (residueSpecMap (Deformation.artinianDualNumbers.{u, u, u} Λ k)) ≅
      SheafOfModules.unit (structureSheafRing (Spec (CommRingCat.of k)).toRingedSpace) :=
  residueConormalIsoUnit _ artinianDualNumbersCoordinate

/-- **The conormal sheaf of the special fibre of a deformation over the dual numbers is the
structure sheaf of the scheme being deformed**: `Deformation.Examples.deformationConormalIsoUnit`
with its hypothesis discharged by `Deformation.Examples.artinianDualNumbersCoordinate`, carried
along an isomorphism of the base object with the dual-number object of `𝒞_Λ`. -/
def dualNumbersDeformationConormalIsoUnit
    (P : SchemeDeformationCategory (Λ := Λ) (k := k) X)
    (hP : P.base ≃ₐ[Λ] Deformation.artinianDualNumbers.{u, u, u} Λ k) :
    Stacks.Thickenings.immersionConormalSheaf P.specialMap ≅
      SheafOfModules.unit (structureSheafRing X.left.toRingedSpace) :=
  deformationConormalIsoUnit P (hP.trans artinianDualNumbersCoordinate)

end Deformation.Examples

end
