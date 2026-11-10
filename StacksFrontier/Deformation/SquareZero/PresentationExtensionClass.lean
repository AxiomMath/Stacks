module

public import StacksFrontier.Deformation.SquareZero.AlgebraExtensions

/-!
# The extension class read off from a presentation (Stacks 0GPU)

Let `A → B` be a ring map, let `N` be a `B`-module and let `α : P → B` be a presentation of
`B` over `A` with relation ideal `J = Ker(α)`.  Because `Ω_{P/A}` is free, the first Ext group
of the naive cotangent complex `NL(α) : J/J² → Ω_{P/A} ⊗_P B` is the cokernel
`Coker(Hom_B(Ω_{P/A} ⊗_P B, N) → Hom_B(J/J², N))`.  Given a square-zero extension
`0 → N → B' → B → 0` of `A`-algebras, the polynomial algebra `P` lifts `α` to an `A`-algebra
map `α' : P → B'`; the restriction `α'|_J` lands in `N` and factors through a `B`-linear map
`δ : J/J² → N`, because `N` has square zero in `B'`.  **The classification of Stacks 0GPT
sends the extension to the class of `δ` in that cokernel**, which is what this file proves.

The other two clauses of the tag are elsewhere: the identification of `Ext¹_B(NL(α), N)` with
the cokernel is `NaiveCotangent.extOne_naiveCotangentComplex_addEquiv_cokernel` of
`StacksFrontier/RingTheory/NaiveCotangent/ExtCokernel.lean`, and the existence of the lift `α'`
together with the factorisation of `α'|_J` is
`Algebra.Generators.exists_lift_and_cotangentMap_to_squareZeroKernel` of
`StacksFrontier/Deformation/RingThickening/CotangentLift.lean`.

## Main definitions

* `Stacks.Deformation.extensionCokernel`: the cokernel displayed in the tag, for an extension
  of `B` over `A`.
* `Stacks.Deformation.extensionCokernelMap`: the map of cokernels induced by a morphism of
  extensions, that is, precomposition with the induced map of conormal modules.
* `Stacks.Deformation.middleExtension`: the middle ring of a square-zero extension of `B` by
  `N`, read as an extension of `B` over `A` in Mathlib's sense.
* `Stacks.Deformation.conormalOfHom`: the conormal functional `δ : J/J² → N` of a lift.
* `Stacks.Deformation.presentationComparison`: the comparison carrying
  `Ext¹_B(NL_{B/A}, N)`, presented as the cokernel of the canonical presentation `A[B] → B`,
  to the cokernel of `NL(α)`.

## Main results

* `Stacks.Deformation.extensionClass_eq_conormalCokernelClass`: **Stacks 0GPU**, the class of
  a square-zero extension is the class of `δ`.
* `Stacks.Deformation.extensionCokernelMap_eq`: two morphisms of extensions induce the same
  map of cokernels, so the comparison does not depend on the chosen morphism of
  presentations.
* `Stacks.Deformation.presentationCokernelEquiv`: the comparison is an isomorphism, which is
  Stacks 00S1 read on these cokernels.
* `Stacks.Deformation.conormalOfHom_quotient_eq`: the class of `δ` does not depend on the
  chosen lift `α'`, so the statement of the tag is about the extension alone.

## Implementation notes

The source's `Ext¹_B(NL(α), N)` is realised as the cokernel itself, which is how the tag
displays it; the identification with the derived-functor Ext group is the separate clause
recalled above.  The classification of Stacks 0GPT lands in `Ext¹_B(NL_{B/A}, N)` for the
canonical presentation `A[B] → B`, and `Stacks.Deformation.extCokernelIso` presents that group
as the cokernel of the canonical presentation; `presentationComparison` then carries it to the
cokernel of the chosen presentation `α`.

That two lifts of `α` have the same class is Mathlib's homotopy `Algebra.Extension.Hom.sub`
between the two induced maps on conormal modules.  The normalisation of the classification —
that the split extension `B ⋉ N` has class zero — enters as
`conormalOfHom_quotient_eq_zero_of_section`: an extension with an `A`-algebra section admits a
lift killing `J`.

`algebraExtensionProblem A B N` records its own copies of `A`, `B` and `N`, and instance
search does not unfold it to see that they are the ambient ones; `algebraMiddleRing`,
`moduleMiddleKernel` and `kernelEquiv'` restate the structures of a solution with the ambient
spelling, and `canonicalConormalClass` is the residue map into the cokernel in the spelling
`Stacks.Deformation.conormalCokernel` uses.

## References

* [Stacks Project, Tag 0GPU](https://stacks.math.columbia.edu/tag/0GPU)
-/

@[expose] public noncomputable section

universe uA uB uN uι uι' v w w' w''

namespace Stacks.Deformation

section Cokernel

variable {A : Type uA} {B : Type uB} [CommRing A] [CommRing B] [Algebra A B]
  (N : Type uN) [AddCommGroup N] [Module B N]

/-- **The cokernel displayed in Stacks 0GPU.**  For an extension `P → B` of the `A`-algebra
`B` with kernel `J`, this is `Coker(Hom_B(Ω_{P/A} ⊗_P B, N) → Hom_B(J/J², N))`. -/
public abbrev extensionCokernel (E : Algebra.Extension.{w} A B) : Type _ :=
  (E.Cotangent →ₗ[B] N) ⧸ LinearMap.range (LinearMap.lcomp B N E.cotangentComplex)

/-- Precomposition with the conormal map of a morphism of extensions, read on the
cokernels of Stacks 0GPU. -/
public noncomputable def extensionCokernelMap {E : Algebra.Extension.{w} A B}
    {E' : Algebra.Extension.{w'} A B} (f : E.Hom E') :
    extensionCokernel N E' →ₗ[B] extensionCokernel N E :=
  Submodule.mapQ _ _ (LinearMap.lcomp B N (Algebra.Extension.Cotangent.map f)) (by
    rintro u ⟨t, rfl⟩
    refine ⟨t ∘ₗ Algebra.Extension.CotangentSpace.map f, LinearMap.ext fun x ↦ ?_⟩
    simp only [LinearMap.lcomp_apply, LinearMap.comp_apply]
    rw [Algebra.Extension.CotangentSpace.map_cotangentComplex])

/-- The map of cokernels induced by a morphism of extensions sends the class of `u` to the
class of `u` precomposed with the induced map of conormal modules. -/
@[simp]
public lemma extensionCokernelMap_mk {E : Algebra.Extension.{w} A B}
    {E' : Algebra.Extension.{w'} A B} (f : E.Hom E') (u : E'.Cotangent →ₗ[B] N) :
    extensionCokernelMap N f (Submodule.Quotient.mk u) =
      Submodule.Quotient.mk (u ∘ₗ Algebra.Extension.Cotangent.map f) :=
  Submodule.mapQ_apply _ _ _ u

/-- **Homotopy uniqueness on cokernels (Stacks 00S1).**  Any two morphisms of extensions
induce the same map of cokernels: the two conormal maps differ by a map factoring through
the conormal differential. -/
public lemma extensionCokernelMap_eq {E : Algebra.Extension.{w} A B}
    {E' : Algebra.Extension.{w'} A B} (f g : E.Hom E') :
    extensionCokernelMap N f = extensionCokernelMap N g := by
  refine LinearMap.ext fun z ↦ ?_
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [extensionCokernelMap_mk, extensionCokernelMap_mk, Submodule.Quotient.eq]
  refine ⟨u ∘ₗ Algebra.Extension.Hom.sub f g, LinearMap.ext fun x ↦ ?_⟩
  have hx := DFunLike.congr_fun (Algebra.Extension.Cotangent.map_sub_map f g) x
  rw [LinearMap.sub_apply, LinearMap.comp_apply] at hx
  simp only [LinearMap.lcomp_apply, LinearMap.comp_apply, LinearMap.sub_apply]
  rw [← map_sub, hx]

/-- The identity morphism of an extension induces the identity of its cokernel. -/
public lemma extensionCokernelMap_id (E : Algebra.Extension.{w} A B) :
    extensionCokernelMap N (Algebra.Extension.Hom.id E) = LinearMap.id := by
  refine LinearMap.ext fun z ↦ ?_
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [extensionCokernelMap_mk, Algebra.Extension.Cotangent.map_id,
    LinearMap.comp_id, LinearMap.id_apply]

/-- The map of cokernels induced by a composite of morphisms of extensions is the composite
of the induced maps, in the opposite order. -/
public lemma extensionCokernelMap_comp {E : Algebra.Extension.{w} A B}
    {E' : Algebra.Extension.{w'} A B} {E'' : Algebra.Extension.{w''} A B}
    (f : E.Hom E') (g : E'.Hom E'') :
    extensionCokernelMap N (g.comp f) =
      (extensionCokernelMap N f).comp (extensionCokernelMap N g) := by
  refine LinearMap.ext fun z ↦ ?_
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [extensionCokernelMap_mk, LinearMap.comp_apply, extensionCokernelMap_mk,
    extensionCokernelMap_mk]
  refine congrArg Submodule.Quotient.mk (LinearMap.ext fun x ↦ ?_)
  have hx := DFunLike.congr_fun (Algebra.Extension.Cotangent.map_comp E'' f g) x
  rw [LinearMap.comp_apply, LinearMap.restrictScalars_apply] at hx
  simp only [LinearMap.comp_apply]
  exact congrArg u hx

/-- **The cokernel of Stacks 0GPU does not depend on the extension.**  A morphism of
extensions admitting a morphism in the other direction induces an isomorphism of
cokernels. -/
public noncomputable def extensionCokernelEquiv {E : Algebra.Extension.{w} A B}
    {E' : Algebra.Extension.{w'} A B} (f : E.Hom E') (g : E'.Hom E) :
    extensionCokernel N E' ≃ₗ[B] extensionCokernel N E :=
  LinearEquiv.ofLinearMap (extensionCokernelMap N f) (extensionCokernelMap N g)
    (by
      rw [← extensionCokernelMap_comp, extensionCokernelMap_eq N (g.comp f)
        (Algebra.Extension.Hom.id E), extensionCokernelMap_id])
    (by
      rw [← extensionCokernelMap_comp, extensionCokernelMap_eq N (f.comp g)
        (Algebra.Extension.Hom.id E'), extensionCokernelMap_id])

/-- **Stacks 00S1 on the cokernels of Stacks 0GPU.**  The cokernel attached to a
presentation of `B` over `A` is independent of the presentation. -/
public noncomputable def presentationCokernelEquiv {ι : Type uι} {ι' : Type uι'}
    (P : Algebra.Generators A B ι) (P' : Algebra.Generators A B ι') :
    extensionCokernel N P'.toExtension ≃ₗ[B] extensionCokernel N P.toExtension :=
  extensionCokernelEquiv N (Algebra.Generators.defaultHom P P').toExtensionHom
    (Algebra.Generators.defaultHom P' P).toExtensionHom

end Cokernel


variable {A : Type uA} {B : Type uB} [CommRing A] [CommRing B] [Algebra A B]
  {N : Type uN} [AddCommGroup N] [Module B N]

/-- On the conormal module of an extension, the action of a scalar is the action of the
chosen section of that scalar. -/
public lemma cotangent_smul_eq_sigma_smul
    (E : Algebra.Extension.{v} A B) (b : B) (z : E.Cotangent) :
    b • z = E.σ b • z :=
  Algebra.Extension.Cotangent.ext (by
    rw [Algebra.Extension.Cotangent.val_smul, Algebra.Extension.Cotangent.val_smul'])

/-- The middle ring of a square-zero extension of the `A`-algebra `B` by `N` is an
`A`-algebra: the lower-left ring of `algebraExtensionProblem A B N` is `A` itself, but
instance search does not unfold the problem to see it. -/
public instance algebraMiddleRing
    {X : (algebraExtensionProblem A B N).CompatibleExtension.{v}} : Algebra A X.B' :=
  X.algebraA'B'

/-- A square-zero extension of the `A`-algebra `B` by `N`, read as an extension of `B` over
`A` in Mathlib's sense. -/
public noncomputable def middleExtension
    (X : (algebraExtensionProblem A B N).CompatibleExtension.{v}) :
    Algebra.Extension.{v} A B :=
  Algebra.Extension.ofSurjective (show X.B' →ₐ[A] B from X.toB) X.surjective

/-- The structure map of the middle extension to `B` is the map `X.B' → B` of the square-zero
extension. -/
@[simp]
public lemma middleExtension_algebraMap
    (X : (algebraExtensionProblem A B N).CompatibleExtension.{v}) (x : X.B') :
    algebraMap (middleExtension X).Ring B x = X.toB x := rfl

/-- An element of the middle ring mapping to zero in `B` lies in the kernel of the middle
extension. -/
public lemma mem_middleExtension_ker
    {X : (algebraExtensionProblem A B N).CompatibleExtension.{v}} {x : X.B'}
    (hx : X.toB x = 0) : x ∈ (middleExtension X).ker := hx

/-- An element of the kernel of the middle extension maps to zero in `B`. -/
public lemma toB_eq_zero_of_mem_middleExtension_ker
    {X : (algebraExtensionProblem A B N).CompatibleExtension.{v}} {x : X.B'}
    (hx : x ∈ (middleExtension X).ker) : X.toB x = 0 := hx

/-- The canonical `B`-module structure on the kernel of a square-zero extension, with its
scalars spelled `B` rather than as the target of the extension problem.  Instance search
does not unfold `algebraExtensionProblem` to see that the two agree. -/
public instance moduleMiddleKernel
    {X : (algebraExtensionProblem A B N).CompatibleExtension.{v}} :
    Module B (RingHom.ker X.toB.toRingHom) :=
  X.moduleKernel

section MiddleExtension

variable (X : (algebraExtensionProblem A B N).CompatibleExtension.{v})

/-- The chosen identification of the kernel of `X.B' → B` with `N`, with its scalars spelled
`B`. -/
public noncomputable def kernelEquiv' : N ≃ₗ[B] RingHom.ker X.toB.toRingHom :=
  X.kernelEquiv

/-- The element of the middle ring which the chosen identification of the kernel assigns to
an element of `N`. -/
public noncomputable def kernelVal (n : N) : X.B' :=
  ((kernelEquiv' X n : RingHom.ker X.toB.toRingHom) : X.B')

/-- The element of the middle ring attached to an element of `N` maps to zero in `B`. -/
@[simp]
public lemma toB_kernelVal (n : N) : X.toB (kernelVal X n) = 0 :=
  (kernelEquiv' X n).2

/-- The element of the middle ring attached to an element of `N` is additive in it. -/
@[simp]
public lemma kernelVal_add (n m : N) :
    kernelVal X (n + m) = kernelVal X n + kernelVal X m :=
  congrArg Subtype.val (map_add (kernelEquiv' X) n m)

/-- The element of the middle ring attached to `0 : N` is zero. -/
@[simp]
public lemma kernelVal_zero : kernelVal X (0 : N) = 0 :=
  congrArg Subtype.val (map_zero (kernelEquiv' X))

/-- Scalar multiplication on `N` is multiplication by any lift of the scalar. -/
public lemma kernelVal_smul (b' : X.B') (b : B) (hb : X.toB b' = b) (n : N) :
    kernelVal X (b • n) = b' * kernelVal X n := by
  have h : (b • kernelEquiv' X n : RingHom.ker X.toB.toRingHom) =
      b' • kernelEquiv' X n := by
    rw [← hb]
    exact X.toB_smul_kernel b' (kernelEquiv' X n)
  exact (congrArg Subtype.val (map_smul (kernelEquiv' X) b n)).trans
    (congrArg Subtype.val h)

/-- The kernel of a square-zero extension squares to zero. -/
public lemma eq_zero_of_mem_sq {x : X.B'}
    (hx : x ∈ RingHom.ker X.toB.toRingHom ^ 2) : x = 0 := by
  rw [X.sq_zero, Ideal.mem_bot] at hx
  exact hx

/-- Distinct elements of `N` give distinct elements of the middle ring. -/
public lemma kernelVal_injective : Function.Injective (kernelVal X) := fun _ _ h ↦
  (kernelEquiv' X).injective (Subtype.ext h)

/-- Every element of the middle ring mapping to zero in `B` is attached to an element of
`N`. -/
public lemma exists_kernelVal_eq {x : X.B'} (hx : X.toB x = 0) :
    ∃ n : N, kernelVal X n = x :=
  ⟨(kernelEquiv' X).symm ⟨x, hx⟩,
    congrArg Subtype.val ((kernelEquiv' X).apply_symm_apply ⟨x, hx⟩)⟩

/-- The element of the relation ideal of the middle extension attached to an element
of `N`. -/
public noncomputable def kernelElt (n : N) : (middleExtension X).ker :=
  ⟨kernelVal X n, mem_middleExtension_ker (toB_kernelVal X n)⟩

/-- `N`, mapped into the conormal module of the middle extension. -/
public noncomputable def toMiddleCotangent : N →ₗ[B] (middleExtension X).Cotangent where
  toFun n := Algebra.Extension.Cotangent.mk (kernelElt X n)
  map_add' n m :=
    (congrArg Algebra.Extension.Cotangent.mk (Subtype.ext (kernelVal_add X n m))).trans
      (map_add Algebra.Extension.Cotangent.mk _ _)
  map_smul' b n := by
    have hσ : X.toB (show X.B' from (middleExtension X).σ b) = b :=
      (middleExtension X).algebraMap_σ b
    refine Eq.trans ?_
      (cotangent_smul_eq_sigma_smul (middleExtension X) b _).symm
    refine Eq.trans ?_ (map_smul Algebra.Extension.Cotangent.mk _ _)
    exact congrArg Algebra.Extension.Cotangent.mk
      (Subtype.ext (kernelVal_smul X (show X.B' from (middleExtension X).σ b) b hσ n))

/-- The map from `N` to the conormal module of the middle extension sends `n` to the class
of its element of the relation ideal. -/
public lemma toMiddleCotangent_apply (n : N) :
    toMiddleCotangent X n = Algebra.Extension.Cotangent.mk (kernelElt X n) := rfl

/-- The identification of `N` with the conormal module of the middle extension: `N` is the
kernel of `X.B' → B`, and that kernel has square zero, so it is its own conormal module. -/
public noncomputable def middleCotangentEquiv : N ≃ₗ[B] (middleExtension X).Cotangent := by
  refine LinearEquiv.ofBijective (toMiddleCotangent X) ⟨?_, ?_⟩
  · intro n m hnm
    refine kernelVal_injective X ?_
    rw [toMiddleCotangent_apply, toMiddleCotangent_apply, ← sub_eq_zero,
      ← map_sub Algebra.Extension.Cotangent.mk,
      Algebra.Extension.Cotangent.mk_eq_zero_iff] at hnm
    exact sub_eq_zero.1 (eq_zero_of_mem_sq X hnm)
  · intro z
    obtain ⟨y, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective z
    obtain ⟨n, hn⟩ := exists_kernelVal_eq X
      (toB_eq_zero_of_mem_middleExtension_ker y.2)
    exact ⟨n, (toMiddleCotangent_apply X n).trans
      (congrArg Algebra.Extension.Cotangent.mk (Subtype.ext hn))⟩

/-- The identification of `N` with the conormal module of the middle extension sends `n` to
the class of its element of the relation ideal. -/
public lemma middleCotangentEquiv_apply (n : N) :
    middleCotangentEquiv X n = Algebra.Extension.Cotangent.mk (kernelElt X n) := rfl

/-- The inverse identification sends the class of an element of the relation ideal to the
element of `N` attached to it. -/
public lemma middleCotangentEquiv_symm_mk (y : (middleExtension X).ker) (n : N)
    (hn : kernelElt X n = y) :
    (middleCotangentEquiv X).symm (Algebra.Extension.Cotangent.mk y) = n := by
  refine (middleCotangentEquiv X).injective ?_
  rw [LinearEquiv.apply_symm_apply, middleCotangentEquiv_apply, hn]

/-- The conormal module of the middle extension is its kernel: the quotient map is
injective because the kernel has square zero. -/
public lemma middleExtension_mk_injective :
    Function.Injective (Algebra.Extension.Cotangent.mk (P := middleExtension X)) := by
  intro u w h
  rw [← sub_eq_zero, ← map_sub, Algebra.Extension.Cotangent.mk_eq_zero_iff] at h
  exact sub_eq_zero.1 (Subtype.ext (eq_zero_of_mem_sq X h))

/-- The element of the relation ideal attached to the inverse image of the class of `w` is
`w` itself. -/
public lemma kernelElt_middleCotangentEquiv_symm_mk (w : (middleExtension X).ker) :
    kernelElt X ((middleCotangentEquiv X).symm (Algebra.Extension.Cotangent.mk w)) = w :=
  middleExtension_mk_injective X (by
    rw [← middleCotangentEquiv_apply, LinearEquiv.apply_symm_apply])

/-- The element of the middle ring attached to the inverse image of the class of `w` is the
underlying element of `w`. -/
public lemma kernelVal_middleCotangentEquiv_symm_mk (w : (middleExtension X).ker) :
    kernelVal X ((middleCotangentEquiv X).symm (Algebra.Extension.Cotangent.mk w)) =
      (w : (middleExtension X).Ring) :=
  congrArg Subtype.val (kernelElt_middleCotangentEquiv_symm_mk X w)

section Source

variable (E : Algebra.Extension.{w} A B)

/-- An `A`-algebra lift of the presentation through the square-zero extension, read as a
morphism of extensions. -/
public noncomputable def liftHom (lift : E.Ring →ₐ[A] X.B')
    (hlift : ∀ p, X.toB (lift p) = algebraMap E.Ring B p) :
    E.Hom (middleExtension X) :=
  Algebra.Extension.Hom.ofAlgHom lift (by ext p; exact hlift p)

/-- The ring map underlying the morphism of extensions of a lift is the lift. -/
@[simp]
public lemma liftHom_toRingHom (lift : E.Ring →ₐ[A] X.B')
    (hlift : ∀ p, X.toB (lift p) = algebraMap E.Ring B p) (p : E.Ring) :
    (liftHom X E lift hlift).toRingHom p = lift p := rfl

/-- **The conormal functional of a lift.**  The restriction of a lift `α' : P → B'` of the
presentation to the relation ideal `J` factors through `J/J²`; this is the resulting
`B`-linear map `J/J² → N`. -/
public noncomputable def conormalOfHom (f : E.Hom (middleExtension X)) :
    E.Cotangent →ₗ[B] N :=
  (middleCotangentEquiv X).symm.toLinearMap ∘ₗ Algebra.Extension.Cotangent.map f

/-- The conormal functional of a lift is the lift, on the relation ideal. -/
public lemma kernelVal_conormalOfHom_mk (f : E.Hom (middleExtension X))
    (y : E.ker) :
    kernelVal X (conormalOfHom X E f (Algebra.Extension.Cotangent.mk y)) =
      f.toRingHom (y : E.Ring) := by
  change kernelVal X ((middleCotangentEquiv X).symm
    (Algebra.Extension.Cotangent.map f (Algebra.Extension.Cotangent.mk y))) = _
  rw [Algebra.Extension.Cotangent.map_mk]
  exact kernelVal_middleCotangentEquiv_symm_mk X _

/-- A `B`-linear map on `J/J²` which restricts to a lift on the relation ideal is the
conormal functional of that lift. -/
public lemma eq_conormalOfHom (f : E.Hom (middleExtension X))
    (δ : E.Cotangent →ₗ[B] N)
    (hδ : ∀ y : E.ker,
      kernelVal X (δ (Algebra.Extension.Cotangent.mk y)) =
        f.toRingHom (y : E.Ring)) :
    δ = conormalOfHom X E f := by
  refine LinearMap.ext fun x ↦ ?_
  obtain ⟨y, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective x
  exact kernelVal_injective X ((hδ y).trans (kernelVal_conormalOfHom_mk X E f y).symm)

/-- **Two lifts differ by a functional through the conormal differential.**  This is
Mathlib's homotopy `Algebra.Extension.Hom.sub` between the two induced maps on conormal
modules, read in `N`. -/
public lemma conormalOfHom_sub (f g : E.Hom (middleExtension X)) :
    conormalOfHom X E f - conormalOfHom X E g =
      ((middleCotangentEquiv X).symm.toLinearMap ∘ₗ Algebra.Extension.Hom.sub f g) ∘ₗ
        E.cotangentComplex := by
  refine LinearMap.ext fun x ↦ ?_
  have hx := DFunLike.congr_fun (Algebra.Extension.Cotangent.map_sub_map f g) x
  rw [LinearMap.sub_apply, LinearMap.comp_apply] at hx
  change (middleCotangentEquiv X).symm (Algebra.Extension.Cotangent.map f x) -
      (middleCotangentEquiv X).symm (Algebra.Extension.Cotangent.map g x) = _
  rw [← map_sub, hx]
  rfl

/-- **The class of the conormal functional does not depend on the lift.** -/
public lemma conormalOfHom_quotient_eq (f g : E.Hom (middleExtension X)) :
    (Submodule.Quotient.mk (conormalOfHom X E f) : extensionCokernel N E) =
      Submodule.Quotient.mk (conormalOfHom X E g) := by
  rw [Submodule.Quotient.eq]
  exact ⟨(middleCotangentEquiv X).symm.toLinearMap ∘ₗ Algebra.Extension.Hom.sub f g,
    (conormalOfHom_sub X E f g).symm⟩

/-- A lift which kills the relation ideal has zero conormal functional. -/
public lemma conormalOfHom_eq_zero (f : E.Hom (middleExtension X))
    (hf : ∀ y : E.ker, f.toRingHom (y : E.Ring) = 0) : conormalOfHom X E f = 0 := by
  exact (eq_conormalOfHom X E f 0 fun y ↦ (kernelVal_zero X).trans (hf y).symm).symm

/-- **An extension admitting an `A`-algebra section has vanishing conormal class.**
Composing the section with the presentation gives a lift which kills the relation ideal. -/
public lemma conormalOfHom_quotient_eq_zero_of_section (f : E.Hom (middleExtension X))
    (s : B →ₐ[A] X.B') (hs : ∀ b, X.toB (s b) = b) :
    (Submodule.Quotient.mk (conormalOfHom X E f) : extensionCokernel N E) = 0 := by
  have hlift : ∀ p : E.Ring,
      X.toB (s.comp (IsScalarTower.toAlgHom A E.Ring B) p) = algebraMap E.Ring B p :=
    fun p ↦ hs _
  rw [conormalOfHom_quotient_eq X E f
      (liftHom X E (s.comp (IsScalarTower.toAlgHom A E.Ring B)) hlift),
    conormalOfHom_eq_zero X E _ fun y ↦ by
      change s (algebraMap E.Ring B (y : E.Ring)) = 0
      rw [show algebraMap E.Ring B (y : E.Ring) = 0 from y.2, map_zero]]
  exact Submodule.Quotient.mk_zero _

/-- The conormal functional of a lift, pulled back along a morphism of extensions, is the
conormal functional of the composed lift. -/
public lemma conormalOfHom_comp (E' : Algebra.Extension.{w'} A B)
    (ψ : E'.Hom E) (f : E.Hom (middleExtension X)) :
    conormalOfHom X E' (f.comp ψ) =
      conormalOfHom X E f ∘ₗ Algebra.Extension.Cotangent.map ψ := by
  refine LinearMap.ext fun x ↦ ?_
  have hx := DFunLike.congr_fun
    (Algebra.Extension.Cotangent.map_comp (middleExtension X) ψ f) x
  rw [LinearMap.comp_apply, LinearMap.restrictScalars_apply] at hx
  change (middleCotangentEquiv X).symm (Algebra.Extension.Cotangent.map (f.comp ψ) x) = _
  rw [hx]
  rfl

end Source

end MiddleExtension

section Classification

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

variable (A : Type uA) (B : Type uB) [CommRing A] [CommRing B] [Algebra A B]
  (N : Type uN) [AddCommGroup N] [Module B N]

/-- The split square-zero extension `B ⋉ N` has the `A`-algebra section `b ↦ (b, 0)`. -/
public noncomputable def splitSection :
    B →ₐ[A] (splitAlgebraExtension A B N).B' :=
  letI opToB : Bᵐᵒᵖ →+* B :=
    { toFun := MulOpposite.unop
      map_one' := rfl
      map_mul' := by intro x y; exact mul_comm _ _
      map_zero' := rfl
      map_add' := by intro x y; rfl }
  letI : Module Bᵐᵒᵖ N := Module.compHom N opToB
  letI : IsCentralScalar B N := ⟨fun _ _ ↦ rfl⟩
  letI : Module A N := Module.compHom N (algebraMap A B)
  letI : IsScalarTower A B N := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : Algebra A (TrivSqZeroExt B N) := TrivSqZeroExt.algebra' A B N
  TrivSqZeroExt.inlAlgHom A B N

/-- The section `b ↦ (b, 0)` of the split extension is a section of its map to `B`. -/
public lemma toB_splitSection (b : B) :
    (splitAlgebraExtension A B N).toB (splitSection A B N b) = b := rfl

variable {A B N}

/-- Evaluation at the chosen lifts of the variables, as a lift of the canonical
presentation `A[B] → B` through a square-zero extension. -/
public noncomputable def solutionLiftHom
    (X : (algebraExtensionProblem A B N).CompatibleExtension.{max uB uN}) :
    (Algebra.Generators.self A B).toExtension.Hom (middleExtension X) :=
  liftHom X (Algebra.Generators.self A B).toExtension (solutionEval X)
    fun p ↦ toB_solutionEval X p

/-- On the class of a reduced relation, the conormal functional of the canonical lift is
the evaluation of the relation in the solution. -/
public lemma conormalOfHom_solutionLiftHom_reducedRelation
    (X : (algebraExtensionProblem A B N).CompatibleExtension.{max uB uN})
    (x : RingHom.ker (problemPresentationToB (algebraExtensionProblem A B N))) :
    conormalOfHom X (Algebra.Generators.self A B).toExtension (solutionLiftHom X)
        (Algebra.Extension.Cotangent.mk
          (reducedRelationOf (algebraExtensionProblem A B N) x)) =
      solutionRelationEval X x := by
  refine kernelVal_injective X (Eq.trans (kernelVal_conormalOfHom_mk X
    (Algebra.Generators.self A B).toExtension (solutionLiftHom X) _) ?_)
  have hid : (MvPolynomial.map (algebraMap A A)) x.1 = x.1 := MvPolynomial.map_id x.1
  exact (congrArg (fun q ↦ solutionEval X q) hid).trans
    (kernelInclusion_solutionRelationEval X x).symm

/-- **The obstruction functional of Stacks 08S5, between the split extension and `X`, is the
difference of the conormal functionals of the two canonical lifts.** -/
public lemma obstructionFunctional_split_eq
    (X : (algebraExtensionProblem A B N).CompatibleExtension.{max uB uN}) :
    (obstructionFunctional (splitAlgebraExtension A B N) X :
        (Algebra.Generators.self A B).toExtension.Cotangent →ₗ[B] N) =
      conormalOfHom X (Algebra.Generators.self A B).toExtension (solutionLiftHom X) -
        conormalOfHom (splitAlgebraExtension A B N)
          (Algebra.Generators.self A B).toExtension
          (solutionLiftHom (splitAlgebraExtension A B N)) := by
  refine conormalFunctional_ext fun x ↦ ?_
  refine (obstructionFunctional_mk _ _ x).trans ?_
  exact congrArg₂ HSub.hSub (conormalOfHom_solutionLiftHom_reducedRelation X x).symm
    (conormalOfHom_solutionLiftHom_reducedRelation (splitAlgebraExtension A B N) x).symm

/-- The obstruction class of Stacks 08S5 is, under the Ext--cokernel comparison, the class
of the obstruction functional. -/
public lemma extCokernelIso_obstructionClass
    (X Y : (algebraExtensionProblem A B N).CompatibleExtension.{max uB uN}) :
    extCokernelIso A B N (obstructionClass (comparisonDiagram X Y)).1 =
      obstructionCokernelClass X Y :=
  AddEquiv.apply_symm_apply _ _

/-- **The classification of Stacks 0GPT, read in the conormal cokernel.**  The class of a
solution is its obstruction class relative to the split extension. -/
public lemma extCokernelIso_squareZeroAlgebraExtensionClassesEquivExtOne
    (X : (algebraExtensionProblem A B N).CompatibleExtension.{max uB uN}) :
    extCokernelIso A B N (squareZeroAlgebraExtensionClassesEquivExtOne A B N
        (Quotient.mk (SquareZeroExtensionProblem.CompatibleExtension.isomorphicSetoid
          (algebraExtensionProblem A B N)) X)) =
      obstructionCokernelClass (splitAlgebraExtension A B N) X := by
  have hsub := squareZeroAlgebraExtensionClassesEquivExtOne_sub A B N
    (splitAlgebraExtension A B N) X
  rw [squareZeroAlgebraExtensionClassesEquivExtOne_split_eq_zero, sub_zero] at hsub
  rw [hsub]
  exact extCokernelIso_obstructionClass (splitAlgebraExtension A B N) X

/-- The residue class of a conormal functional of the canonical presentation `A[B] → B`,
in the cokernel which presents `Ext¹_B(NL_{B/A}, N)`. -/
public noncomputable def canonicalConormalClass
    (u : (Algebra.Generators.self A B).toExtension.Cotangent →ₗ[B] N) :
    conormalCokernel (algebraExtensionProblem A B N) :=
  Submodule.Quotient.mk u

/-- The residue class of a difference of conormal functionals is the difference of the
residue classes. -/
public lemma canonicalConormalClass_sub
    (a b : (Algebra.Generators.self A B).toExtension.Cotangent →ₗ[B] N) :
    canonicalConormalClass (a - b) =
      canonicalConormalClass a - canonicalConormalClass b := rfl

/-- A conormal functional through the conormal differential has residue class zero. -/
public lemma canonicalConormalClass_eq_zero
    (b : (Algebra.Generators.self A B).toExtension.Cotangent →ₗ[B] N)
    (hb : b ∈ LinearMap.range (LinearMap.lcomp B N
      (Algebra.Generators.self A B).toExtension.cotangentComplex)) :
    canonicalConormalClass b = 0 :=
  (Submodule.Quotient.mk_eq_zero _).2 hb

/-- Subtracting a conormal functional through the conormal differential does not change
the residue class. -/
public lemma canonicalConormalClass_sub_eq
    (a b : (Algebra.Generators.self A B).toExtension.Cotangent →ₗ[B] N)
    (hb : b ∈ LinearMap.range (LinearMap.lcomp B N
      (Algebra.Generators.self A B).toExtension.cotangentComplex)) :
    canonicalConormalClass (a - b) = canonicalConormalClass a := by
  rw [canonicalConormalClass_sub, canonicalConormalClass_eq_zero b hb, sub_zero]

/-- The obstruction cokernel class of `X` and `Y` is the residue class of their obstruction
functional. -/
public lemma obstructionCokernelClass_eq_canonicalConormalClass
    (X Y : (algebraExtensionProblem A B N).CompatibleExtension.{max uB uN}) :
    obstructionCokernelClass X Y = canonicalConormalClass (obstructionFunctional X Y) := rfl

/-- The conormal functional of the canonical lift of the split extension is a coboundary. -/
public lemma conormalOfHom_solutionLiftHom_split_mem_range :
    conormalOfHom (splitAlgebraExtension A B N) (Algebra.Generators.self A B).toExtension
        (solutionLiftHom (splitAlgebraExtension A B N)) ∈
      LinearMap.range (LinearMap.lcomp B N
        (Algebra.Generators.self A B).toExtension.cotangentComplex) := by
  rw [← Submodule.Quotient.mk_eq_zero]
  exact conormalOfHom_quotient_eq_zero_of_section (splitAlgebraExtension A B N)
    (Algebra.Generators.self A B).toExtension
    (solutionLiftHom (splitAlgebraExtension A B N)) (splitSection A B N)
    (toB_splitSection A B N)

/-- **The class of a square-zero extension, as a conormal class.**  The obstruction class
of Stacks 08S5 between the split extension and `X` is the class of the conormal functional of
the canonical lift of `X`. -/
public lemma obstructionCokernelClass_split_eq_canonicalConormalClass
    (X : (algebraExtensionProblem A B N).CompatibleExtension.{max uB uN}) :
    obstructionCokernelClass (splitAlgebraExtension A B N) X =
      canonicalConormalClass
        (conormalOfHom X (Algebra.Generators.self A B).toExtension (solutionLiftHom X)) := by
  refine Eq.trans (obstructionCokernelClass_eq_canonicalConormalClass _ X) ?_
  exact (congrArg canonicalConormalClass (obstructionFunctional_split_eq X)).trans
    (canonicalConormalClass_sub_eq _ _ conormalOfHom_solutionLiftHom_split_mem_range)

/-- **The comparison of Stacks 00S1 on the cokernels of Stacks 0GPU.**  It carries
`Ext¹_B(NL_{B/A}, N)`, presented as the cokernel of the canonical presentation `A[B] → B`, to
the cokernel of a presentation `α : P → B`, along a morphism of presentations `ψ : P → A[B]`.
It is an isomorphism by `presentationCokernelEquiv`, and independent of `ψ` by
`extensionCokernelMap_eq`. -/
public noncomputable def presentationComparison
    {ι : Type uι} (P : Algebra.Generators A B ι)
    (ψ : P.toExtension.Hom (Algebra.Generators.self A B).toExtension) :
    conormalCokernel (algebraExtensionProblem A B N) → extensionCokernel N P.toExtension :=
  extensionCokernelMap N ψ

/-- The comparison sends the residue class of `u` to the class of `u` precomposed with the
map of conormal modules induced by `ψ`. -/
public lemma presentationComparison_canonicalConormalClass
    {ι : Type uι} (P : Algebra.Generators A B ι)
    (ψ : P.toExtension.Hom (Algebra.Generators.self A B).toExtension)
    (u : (Algebra.Generators.self A B).toExtension.Cotangent →ₗ[B] N) :
    presentationComparison P ψ (canonicalConormalClass u) =
      Submodule.Quotient.mk (u ∘ₗ Algebra.Extension.Cotangent.map ψ) :=
  extensionCokernelMap_mk N ψ u

/-- A polynomial presentation lifts through a square-zero extension, and the lift factors
through the conormal module, so the hypotheses of `extensionClass_eq_conormalCokernelClass`
are satisfiable for every presentation and every extension. -/
public lemma exists_lift_and_conormal
    {ι : Type uι} (P : Algebra.Generators A B ι)
    (X : (algebraExtensionProblem A B N).CompatibleExtension.{max uB uN}) :
    ∃ (lift : P.Ring →ₐ[A] X.B') (_ : ∀ p, X.toB (lift p) = algebraMap P.Ring B p)
      (δ : P.toExtension.Cotangent →ₗ[B] N),
      ∀ y : P.toExtension.ker,
        kernelVal X (δ (Algebra.Extension.Cotangent.mk y)) =
          lift (y : P.toExtension.Ring) := by
  let g : P.Ring →ₐ[A] X.B' :=
    MvPolynomial.aeval fun i ↦ (middleExtension X).σ (P.val i)
  have hg : (IsScalarTower.toAlgHom A (middleExtension X).Ring B).comp g =
      IsScalarTower.toAlgHom A P.Ring B := by
    ext i
    have hX : g (MvPolynomial.X i : P.Ring) = (middleExtension X).σ (P.val i) :=
      MvPolynomial.aeval_X _ i
    change algebraMap (middleExtension X).Ring B (g (MvPolynomial.X i : P.Ring)) =
      algebraMap P.Ring B (MvPolynomial.X i : P.Ring)
    rw [hX, (middleExtension X).algebraMap_σ, P.algebraMap_apply, MvPolynomial.aeval_X]
  have hlift : ∀ p, X.toB (g p) = algebraMap P.Ring B p := fun p ↦ congr($hg p)
  exact ⟨g, hlift, conormalOfHom X P.toExtension (liftHom X P.toExtension g hlift),
    kernelVal_conormalOfHom_mk X P.toExtension (liftHom X P.toExtension g hlift)⟩

/-- **Stacks 0GPU, the extension class.**  Let `α : P → B` be a presentation of the
`A`-algebra `B` with relation ideal `J`, let `0 → N → B' → B → 0` be a square-zero extension
of `A`-algebras, let `α' : P → B'` be an `A`-algebra lift of `α`, and let `δ : J/J² → N` be
the `B`-linear factorisation of `α'|_J`.  Then the classification of Stacks 0GPT, carried to
the cokernel `Coker(Hom_B(Ω_{P/A} ⊗_P B, N) → Hom_B(J/J², N))` which computes
`Ext¹_B(NL(α), N)`, sends the extension to the class of `δ`. -/
@[stacks 0GPU "extension_class"]
public theorem extensionClass_eq_conormalCokernelClass
    {ι : Type uι} (P : Algebra.Generators A B ι)
    (X : (algebraExtensionProblem A B N).CompatibleExtension.{max uB uN})
    (lift : P.Ring →ₐ[A] X.B')
    (hlift : ∀ p, X.toB (lift p) = algebraMap P.Ring B p)
    (δ : P.toExtension.Cotangent →ₗ[B] N)
    (hδ : ∀ y : P.toExtension.ker,
      kernelVal X (δ (Algebra.Extension.Cotangent.mk y)) = lift (y : P.toExtension.Ring))
    (ψ : P.toExtension.Hom (Algebra.Generators.self A B).toExtension) :
    presentationComparison P ψ
        (extCokernelIso A B N (squareZeroAlgebraExtensionClassesEquivExtOne A B N
          (Quotient.mk (SquareZeroExtensionProblem.CompatibleExtension.isomorphicSetoid
            (algebraExtensionProblem A B N)) X))) =
      Submodule.Quotient.mk δ := by
  rw [extCokernelIso_squareZeroAlgebraExtensionClassesEquivExtOne,
    obstructionCokernelClass_split_eq_canonicalConormalClass,
    presentationComparison_canonicalConormalClass,
    ← conormalOfHom_comp X (Algebra.Generators.self A B).toExtension P.toExtension ψ
      (solutionLiftHom X),
    eq_conormalOfHom X P.toExtension (liftHom X P.toExtension lift hlift) δ hδ]
  exact conormalOfHom_quotient_eq X P.toExtension _ _

end Classification

end Stacks.Deformation

end
