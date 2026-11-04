module

public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.ReflexivePowerSystem
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.SectionLocusGenericPoint
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCoherence
import StacksFrontier.Topology.Sheaves.OpenImmersion.ModuleExtensionByZero

/-!
# The system of [Stacks, Tag 0EBN] over the isomorphism locus, and its cocone on `j_*𝒪_U`

Let `X` be an integral locally Noetherian normal scheme, `ℱ` a coherent `𝒪_X`-module, `s` a
global section of `ℱ`, and let

`U = {x ∈ X | s : 𝒪_{X, x} → ℱ_x is an isomorphism}`

be the open locus of [Stacks, Tag 0EBN], `AlgebraicGeometry.sectionIsomorphismOpen`.
By construction `s` induces an isomorphism on every stalk at a point of `U`; a morphism of
sheaves of modules which is a stalkwise isomorphism is an isomorphism, so the morphism
`𝒪_X ⟶ ℱ` determined by `s` *restricts to an isomorphism* `𝒪_U ≅ ℱ|_U`.  In particular `ℱ|_U`
is invertible, being isomorphic to the structure sheaf.

Over `U` the system `𝒪_X →ˢ ℱ →ˢ ℱ^{[2]} →ˢ ⋯` of [Stacks, Tag 0EBN] is therefore isomorphic,
as a diagram, to the ordinary tensor-power system of `ℱ|_U` and `s|_U`
(`restrictPowerSystemIso`), and in that system *every transition map is invertible*: the
transition is multiplication by `s|_U`, which is the inverse left unitor followed by whiskering
the isomorphism `𝒪_U ≅ ℱ|_U`.  So the restricted system is a sequence of isomorphisms, its
colimit is its zeroth term `𝒪_U`, and transposing along
`AlgebraicGeometry.Scheme.Modules.restrictAdjunction` turns the resulting cocone over `U` into a
cocone on the system itself with vertex `j_*𝒪_U`.

That cocone is `reflexivePowerSystemPushforwardCocone` below, and read over `U` itself it is
`restrictReflexivePowerSystemCocone`, which is colimiting, all its legs being isomorphisms.
So the colimit clause of [Stacks, Tag 0EBN] holds over `U`.  That the cocone on `X` is
colimiting is proved in `SectionLocusColimitSections.lean`; see "The clause on `X`" below.

## Main definitions

* `Stacks.AlgebraicGeometry.ReflexivePowers.restrictUnitSectionIso`: the trivialization
  `𝒪_U ≅ ℱ|_U` induced by `s`.
* `Stacks.AlgebraicGeometry.ReflexivePowers.tensorPowerUnitIso`: `𝒢^{⊗ n} ≅ 𝒪_Y` for a section
  trivializing `𝒢`, the `n`-fold multiplication by that section read backwards.
* `Stacks.AlgebraicGeometry.ReflexivePowers.restrictReflexivePowerUnitIso`: the leg
  `ℱ^{[n]}|_U ≅ 𝒪_U`, division by `sⁿ`.
* `Stacks.AlgebraicGeometry.ReflexivePowers.reflexivePowerSystemPushforwardCocone`: the cocone
  on `reflexivePowerSystem F s` with vertex `j_*𝒪_U`.
* `Stacks.AlgebraicGeometry.ReflexivePowers.restrictReflexivePowerSystemCocone`: the same legs
  read as a cocone over `U` itself, with vertex `𝒪_U`.
* `Stacks.CategoryTheory.isColimitOfIsIso_ι`: a cocone on an `ℕ`-indexed diagram all of whose
  legs are isomorphisms is colimiting.

## Main results

* `Stacks.AlgebraicGeometry.ReflexivePowers.isIso_restrict_unitHom_sectionIsomorphismOpen`:
  `s` trivializes `ℱ` over `U`.
* `Stacks.AlgebraicGeometry.ReflexivePowers.isInvertible_restrict_sectionIsomorphismOpen`:
  `ℱ|_U` is invertible.
* `Stacks.AlgebraicGeometry.ReflexivePowers.nonempty_sectionIsomorphismOpen`: under the source's
  reflexivity and rank-one hypotheses a nonzero `s` puts the generic point in `U`, which is the
  `Nonempty U` the invertibility machinery asks for.
* `Stacks.AlgebraicGeometry.ReflexivePowers.isIso_tensorPowerTransition`: multiplication by a
  section that trivializes the module is invertible at every stage of the tensor-power system.
* `Stacks.AlgebraicGeometry.ReflexivePowers.isIso_restrict_reflexivePowerTransition`: every
  transition of the system of [Stacks, Tag 0EBN] restricts to an isomorphism over `U`.
* `Stacks.AlgebraicGeometry.ReflexivePowers.isColimitRestrictReflexivePowerSystemCocone`:
  **the colimit clause of [Stacks, Tag 0EBN] holds over `U`** — over `U` the system has colimit
  `𝒪_U`, with the cocone above.

## The clause on `X`

The colimit clause of [Stacks, Tag 0EBN] asserts that `reflexivePowerSystemPushforwardCocone` is
colimiting on `X`.  What is proved here is the clause over `U`,
`isColimitRestrictReflexivePowerSystemCocone`; since restriction to `U` is a left adjoint and so
preserves colimits, that says exactly

`(colim ℱ^{[n]})|_U ≅ 𝒪_U ≅ (j_*𝒪_U)|_U`,

so the comparison `colim ℱ^{[n]} ⟶ j_*𝒪_U` is an isomorphism *over `U`*, and the clause is the
behaviour along `X \ U`, about which the restricted picture says nothing.  The source's argument,
carried out in `SectionLocusColimitSections.lean`, is: on an affine chart `D` inside an open `V`
where `ℱ` is invertible and whose complement has codimension at least two, a section of `𝒪` over
`U ⊓ D` is `a / gᵐ` and the image of `1` in `ℱ^{[m]}` is divisible by `gᵐ`, the local solutions
glue on the quasi-compact `V ⊓ W`, and algebraic Hartogs extension carries the result to `W`.

## References

* [Stacks Project, Tag 0EBN](https://stacks.math.columbia.edu/tag/0EBN)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory

universe v u

attribute [local instance] Stacks.SheafOfModules.OnSpace.monoidal

namespace Stacks.CategoryTheory

/-- **A cocone on an `ℕ`-indexed diagram all of whose legs are isomorphisms is colimiting.**
The map out of the cocone is read off at the index `0`: inverting the leg there and following
another cocone's leg.  That it factors the other cocone at every `n` is the two cocone
identities along `0 ⟶ n`, and it is unique because the leg at `0` is epi. -/
def isColimitOfIsIso_ι {C : Type u} [Category.{v} C] {D : CategoryTheory.Functor ℕ C}
    (c : Limits.Cocone D) (h : ∀ n : ℕ, IsIso (c.ι.app n)) : Limits.IsColimit c where
  desc c' := CategoryTheory.inv (c.ι.app 0) ≫ c'.ι.app 0
  fac c' n := by
    have := h n
    have := h 0
    have hD : D.map (homOfLE (Nat.zero_le n)) =
        c.ι.app 0 ≫ CategoryTheory.inv (c.ι.app n) := by
      rw [← c.w (homOfLE (Nat.zero_le n)), Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    have hc' := c'.w (homOfLE (Nat.zero_le n))
    rw [hD] at hc'
    rw [← hc']
    simp
  uniq c' m hm := by
    have := h 0
    rw [← hm 0, IsIso.inv_hom_id_assoc]

end Stacks.CategoryTheory

namespace Stacks.AlgebraicGeometry.ReflexivePowers

/-! ### Multiplication by an invertible section -/

/-- **Multiplication by an invertible section is invertible.**  `mulSectionHom Z σ` is the
inverse left unitor followed by whiskering `σ`, so it is an isomorphism as soon as `σ` is. -/
theorem isIso_mulSectionHom {Z : RingedSpace.{u, u}}
    {A B : SheafOfModules.{u} (structureSheafRing Z)}
    (σ : 𝟙_ (SheafOfModules.{u} (structureSheafRing Z)) ⟶ A) [IsIso σ] :
    IsIso (mulSectionHom Z σ (G := B)) := by
  show IsIso ((λ_ B).inv ≫ (σ ▷ B))
  infer_instance

/-- **Every transition of the tensor-power system of a trivializing section is invertible.**  In
degree `0` the transition is the morphism `𝒪 ⟶ 𝒢` determined by the section, which is the
hypothesis; in higher degrees it is multiplication by that morphism. -/
theorem isIso_tensorPowerTransition {Y : Scheme.{u}} (G : Y.Modules) (t : G.sections)
    (h : IsIso (G.unitHomEquiv.symm t)) (n : ℕ) :
    IsIso (tensorPowerTransition G t n) := by
  cases n with
  | zero => rw [tensorPowerTransition_zero]; exact h
  | succ n => exact @isIso_mulSectionHom _ _ (tensorPower G (n + 1)) (G.unitHomEquiv.symm t) h

/-! ### The section trivializes the module over its isomorphism locus -/

section Trivialization

variable (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] (F : X.Modules)
  [F.IsCoherent] (s : F.sections)

/-- **A global section trivializes a coherent module over the open locus of [Stacks, Tag 0EBN]
where it trivializes the stalks.**  At a point `y` of `U` the stalk map is invertible by the very
definition of `AlgebraicGeometry.sectionIsomorphismLocus`, the stalk of the restriction at `y` is
the stalk at `y` of the original module
(`AlgebraicGeometry.Scheme.Modules.restrictStalkNatIso`), and a morphism of sheaves of modules
invertible on every stalk is invertible
(`Stacks.ExtensionByZeroModules.isIso_of_stalk_isIso`). -/
theorem isIso_restrict_unitHom_sectionIsomorphismOpen :
    IsIso ((Scheme.Modules.restrictFunctor (sectionIsomorphismOpen X F s).ι).map
      (F.unitHomEquiv.symm s)) := by
  refine ExtensionByZeroModules.isIso_of_stalk_isIso
    (sectionIsomorphismOpen X F s).toScheme.ringCatSheaf _ fun y => ?_
  exact (NatIso.isIso_map_iff
    (Scheme.Modules.restrictStalkNatIso (sectionIsomorphismOpen X F s).ι y)
    (F.unitHomEquiv.symm s)).mpr y.2

/-- **The trivialization `𝒪_U ≅ ℱ|_U`**: the identification `𝒪_X|_U ≅ 𝒪_U` followed by the
restriction of the morphism determined by `s`, which
`isIso_restrict_unitHom_sectionIsomorphismOpen` shows to be invertible. -/
def restrictUnitSectionIso :
    SheafOfModules.unit (sectionIsomorphismOpen X F s).toScheme.ringCatSheaf ≅
      (Scheme.Modules.restrictFunctor (sectionIsomorphismOpen X F s).ι).obj F :=
  (Scheme.Modules.restrictUnitIso (sectionIsomorphismOpen X F s).ι).symm ≪≫
    @asIso _ _ _ _ _ (isIso_restrict_unitHom_sectionIsomorphismOpen X F s)

/-- **`ℱ|_U` is invertible.**  It is isomorphic to the structure sheaf of `U`, which is
invertible, and invertibility only depends on the isomorphism class. -/
theorem isInvertible_restrict_sectionIsomorphismOpen :
    Stacks.SheafOfModules.IsInvertible
      (sectionIsomorphismOpen X F s).toScheme.sheaf.obj
      (sectionIsomorphismOpen X F s).toScheme.ringCatSheaf.property
      ((Scheme.Modules.restrictFunctor (sectionIsomorphismOpen X F s).ι).obj F) :=
  have : Stacks.SheafOfModules.IsInvertible
      (sectionIsomorphismOpen X F s).toScheme.sheaf.obj
      (sectionIsomorphismOpen X F s).toScheme.ringCatSheaf.property
      (SheafOfModules.unit (sectionIsomorphismOpen X F s).toScheme.ringCatSheaf) :=
    Stacks.SheafOfModules.isInvertible_unit _ _
  Stacks.SheafOfModules.isInvertible_of_iso _ _ (restrictUnitSectionIso X F s)

/-- **The isomorphism locus of a nonzero section of a coherent reflexive module of rank one is
nonempty**: it contains the generic point, by
`AlgebraicGeometry.mem_sectionIsomorphismLocus_genericPoint`. -/
theorem nonempty_sectionIsomorphismOpen (hF : ReflexiveModules.IsReflexive F)
    (hrank : Scheme.Modules.fiberRank F (genericPoint X) = 1)
    (hs : s.eval (Opposite.op (⊤ : X.Opens)) ≠ 0) :
    Nonempty (sectionIsomorphismOpen X F s).toScheme :=
  ⟨⟨genericPoint X, mem_sectionIsomorphismLocus_genericPoint F hF hrank s hs⟩⟩

/-- The morphism `𝒪_U ⟶ ℱ|_U` determined by the restricted section `s|_U` is invertible: it is
the trivialization `restrictUnitSectionIso`. -/
theorem isIso_unitHom_restrictSection :
    IsIso (((Scheme.Modules.restrictFunctor (sectionIsomorphismOpen X F s).ι).obj
      F).unitHomEquiv.symm (restrictSection (sectionIsomorphismOpen X F s) F s)) := by
  rw [unitHomEquiv_symm_restrictSection]
  exact (restrictUnitSectionIso X F s).isIso_hom

end Trivialization

/-! ### The cocone on the tensor-power system over the isomorphism locus -/

section TensorCocone

variable {Y : Scheme.{u}} (G : Y.Modules) (t : G.sections)
  (ht : IsIso (G.unitHomEquiv.symm t))

/-- **`(𝒢)^{⊗ n} ≅ 𝒪_Y` for a section that trivializes `𝒢`**, the `n`-fold multiplication by
`t` read backwards.  Every transition of the tensor-power system is invertible by
`isIso_tensorPowerTransition`, so the recursion is "undo one multiplication"; the forward
direction of the isomorphism at `n` is the leg at `n` of a cocone with vertex `𝒪_Y`. -/
def tensorPowerUnitIso : (n : ℕ) → (tensorPower G n ≅ SheafOfModules.unit Y.ringCatSheaf)
  | 0 => Iso.refl _
  | n + 1 => (@asIso _ _ _ _ _ (isIso_tensorPowerTransition G t ht n)).symm ≪≫
      tensorPowerUnitIso n

/-- At `0` the isomorphism is the identity: the zeroth tensor power is the structure sheaf. -/
theorem tensorPowerUnitIso_zero : tensorPowerUnitIso G t ht 0 = Iso.refl _ := rfl

/-- The recursion: the isomorphism at `n + 1` undoes one multiplication by `t`. -/
theorem tensorPowerUnitIso_succ (n : ℕ) :
    tensorPowerUnitIso G t ht (n + 1) =
      (@asIso _ _ _ _ _ (isIso_tensorPowerTransition G t ht n)).symm ≪≫
        tensorPowerUnitIso G t ht n := rfl

/-- **The cocone identity for the tensor-power system**: multiplication by `t` followed by the
leg at `n + 1` is the leg at `n`, because the leg at `n + 1` begins by inverting that
multiplication. -/
theorem tensorPowerTransition_comp_tensorPowerUnitIso_hom (n : ℕ) :
    tensorPowerTransition G t n ≫ (tensorPowerUnitIso G t ht (n + 1)).hom =
      (tensorPowerUnitIso G t ht n).hom :=
  (congrArg (fun e => tensorPowerTransition G t n ≫ Iso.hom e)
      (tensorPowerUnitIso_succ G t ht n)).trans
    ((@asIso _ _ _ _ _ (isIso_tensorPowerTransition G t ht n)).hom_inv_id_assoc _)

end TensorCocone

/-! ### The cocone on the system of Tag 0EBN with vertex `j_*𝒪_U` -/

section Cocone

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] (F : X.Modules)
  [F.IsCoherent] (s : F.sections)
  [Nonempty (AlgebraicGeometry.sectionIsomorphismOpen X F s).toScheme]

/-- **`ℱ^{[n]}|_U ≅ 𝒪_U`**: the comparison of the system of [Stacks, Tag 0EBN] with the
tensor-power system of `ℱ|_U` and `s|_U`, followed by `tensorPowerUnitIso`.  The forward
direction is "divide by `sⁿ`". -/
def restrictReflexivePowerUnitIso (n : ℕ) :
    (Scheme.Modules.restrictFunctor (sectionIsomorphismOpen X F s).ι).obj
        (reflexivePower F n) ≅
      SheafOfModules.unit (sectionIsomorphismOpen X F s).toScheme.ringCatSheaf :=
  restrictPowerIso F (sectionIsomorphismOpen X F s) inferInstance
      (isInvertible_restrict_sectionIsomorphismOpen X F s) n ≪≫
    tensorPowerUnitIso ((Scheme.Modules.restrictFunctor
        (sectionIsomorphismOpen X F s).ι).obj F)
      (restrictSection (sectionIsomorphismOpen X F s) F s)
      (isIso_unitHom_restrictSection X F s) n

/-- The two factors of `restrictReflexivePowerUnitIso`, written out. -/
theorem restrictReflexivePowerUnitIso_eq (n : ℕ) :
    restrictReflexivePowerUnitIso F s n =
      restrictPowerIso F (sectionIsomorphismOpen X F s) inferInstance
          (isInvertible_restrict_sectionIsomorphismOpen X F s) n ≪≫
        tensorPowerUnitIso ((Scheme.Modules.restrictFunctor
            (sectionIsomorphismOpen X F s).ι).obj F)
          (restrictSection (sectionIsomorphismOpen X F s) F s)
          (isIso_unitHom_restrictSection X F s) n := rfl

/-- **The cocone identity over `U`**: the restricted transition `ℱ^{[n]}|_U ⟶ ℱ^{[n + 1]}|_U`
followed by the leg at `n + 1` is the leg at `n`.  This is the transition square
`restrict_reflexivePowerTransition_comp_restrictPowerIso_hom'` followed by
`tensorPowerTransition_comp_tensorPowerUnitIso_hom`. -/
theorem restrict_reflexivePowerTransition_comp_restrictReflexivePowerUnitIso_hom (n : ℕ) :
    (Scheme.Modules.restrictFunctor (sectionIsomorphismOpen X F s).ι).map
          (reflexivePowerTransition F s n) ≫
        (restrictReflexivePowerUnitIso F s (n + 1)).hom =
      (restrictReflexivePowerUnitIso F s n).hom := by
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun k => k ≫ (tensorPowerUnitIso
      ((Scheme.Modules.restrictFunctor (sectionIsomorphismOpen X F s).ι).obj F)
      (restrictSection (sectionIsomorphismOpen X F s) F s)
      (isIso_unitHom_restrictSection X F s) (n + 1)).hom)
    (restrict_reflexivePowerTransition_comp_restrictPowerIso_hom' F
      (sectionIsomorphismOpen X F s) inferInstance
      (isInvertible_restrict_sectionIsomorphismOpen X F s) s n)) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact congrArg (fun k => (restrictPowerIso F (sectionIsomorphismOpen X F s) inferInstance
      (isInvertible_restrict_sectionIsomorphismOpen X F s) n).hom ≫ k)
    (tensorPowerTransition_comp_tensorPowerUnitIso_hom _
      (restrictSection (sectionIsomorphismOpen X F s) F s)
      (isIso_unitHom_restrictSection X F s) n)

/-- **Every transition of the system of [Stacks, Tag 0EBN] restricts to an isomorphism over
`U`.**  Three sides of the transition square are isomorphisms — the two comparisons with the
tensor-power system, and multiplication by `s|_U` — so the fourth is. -/
theorem isIso_restrict_reflexivePowerTransition (n : ℕ) :
    IsIso ((Scheme.Modules.restrictFunctor (sectionIsomorphismOpen X F s).ι).map
      (reflexivePowerTransition F s n)) := by
  have := isIso_tensorPowerTransition ((Scheme.Modules.restrictFunctor
      (sectionIsomorphismOpen X F s).ι).obj F)
    (restrictSection (sectionIsomorphismOpen X F s) F s)
    (isIso_unitHom_restrictSection X F s) n
  have : IsIso ((Scheme.Modules.restrictFunctor (sectionIsomorphismOpen X F s).ι).map
      (reflexivePowerTransition F s n) ≫
        (restrictPowerIso F (sectionIsomorphismOpen X F s) inferInstance
          (isInvertible_restrict_sectionIsomorphismOpen X F s) (n + 1)).hom) := by
    rw [restrict_reflexivePowerTransition_comp_restrictPowerIso_hom']
    infer_instance
  exact IsIso.of_isIso_comp_right _ (restrictPowerIso F (sectionIsomorphismOpen X F s)
    inferInstance (isInvertible_restrict_sectionIsomorphismOpen X F s) (n + 1)).hom

/-- **The cocone on the system of [Stacks, Tag 0EBN] with vertex `j_*𝒪_U`.**  Its leg at `n` is
the transpose along `AlgebraicGeometry.Scheme.Modules.restrictAdjunction` of the isomorphism
`ℱ^{[n]}|_U ≅ 𝒪_U` of `restrictReflexivePowerUnitIso`, which over `U` is division by `sⁿ`.

This is the cocone of the colimit clause of [Stacks, Tag 0EBN]. -/
def reflexivePowerSystemPushforwardCocone : Limits.Cocone (reflexivePowerSystem F s) where
  pt := (Scheme.Modules.pushforward (sectionIsomorphismOpen X F s).ι).obj
    (SheafOfModules.unit (sectionIsomorphismOpen X F s).toScheme.ringCatSheaf)
  ι := NatTrans.ofSequence
    (fun n => (Scheme.Modules.restrictAdjunction (sectionIsomorphismOpen X F s).ι).homEquiv
      (reflexivePower F n)
      (SheafOfModules.unit (sectionIsomorphismOpen X F s).toScheme.ringCatSheaf)
      (restrictReflexivePowerUnitIso F s n).hom)
    fun n => by
      refine Eq.trans (congrArg (fun φ => φ ≫
        (Scheme.Modules.restrictAdjunction (sectionIsomorphismOpen X F s).ι).homEquiv
          (reflexivePower F (n + 1))
          (SheafOfModules.unit (sectionIsomorphismOpen X F s).toScheme.ringCatSheaf)
          (restrictReflexivePowerUnitIso F s (n + 1)).hom)
        (reflexivePowerSystem_map_succ F s n)) ?_
      refine Eq.trans ?_ (Category.comp_id _).symm
      refine Eq.trans (Adjunction.homEquiv_naturality_left _ _ _).symm ?_
      exact congrArg _
        (restrict_reflexivePowerTransition_comp_restrictReflexivePowerUnitIso_hom F s n)

/-- The leg of the cocone at `n` is the transpose of division by `sⁿ` over `U`. -/
theorem reflexivePowerSystemPushforwardCocone_ι_app (n : ℕ) :
    (reflexivePowerSystemPushforwardCocone F s).ι.app n =
      (Scheme.Modules.restrictAdjunction (sectionIsomorphismOpen X F s).ι).homEquiv
        (reflexivePower F n)
        (SheafOfModules.unit (sectionIsomorphismOpen X F s).toScheme.ringCatSheaf)
        (restrictReflexivePowerUnitIso F s n).hom := rfl

/-- **The cocone over `U` itself**, on the restricted system
`𝒪_U →^{s|_U} ℱ|_U →^{s|_U} ℱ^{[2]}|_U → ⋯`, with vertex `𝒪_U` and legs the isomorphisms
`restrictReflexivePowerUnitIso`.  It is the restriction of
`reflexivePowerSystemPushforwardCocone` read through `j^*j_* = id`. -/
def restrictReflexivePowerSystemCocone : Limits.Cocone (reflexivePowerSystem F s ⋙
    Scheme.Modules.restrictFunctor (sectionIsomorphismOpen X F s).ι) where
  pt := SheafOfModules.unit (sectionIsomorphismOpen X F s).toScheme.ringCatSheaf
  ι := NatTrans.ofSequence (fun n => (restrictReflexivePowerUnitIso F s n).hom) fun n => by
    refine Eq.trans (congrArg (fun φ => φ ≫ (restrictReflexivePowerUnitIso F s (n + 1)).hom)
      (congrArg (Scheme.Modules.restrictFunctor (sectionIsomorphismOpen X F s).ι).map
        (reflexivePowerSystem_map_succ F s n))) ?_
    refine Eq.trans ?_ (Category.comp_id _).symm
    exact restrict_reflexivePowerTransition_comp_restrictReflexivePowerUnitIso_hom F s n

/-- The leg of the cocone over `U` at `n` is division by `sⁿ`. -/
theorem restrictReflexivePowerSystemCocone_ι_app (n : ℕ) :
    (restrictReflexivePowerSystemCocone F s).ι.app n =
      (restrictReflexivePowerUnitIso F s n).hom := rfl

/-- **The colimit clause of [Stacks, Tag 0EBN] over the isomorphism locus itself**: over `U` the
system `𝒪_X →ˢ ℱ →ˢ ℱ^{[2]} →ˢ ⋯` has colimit `𝒪_U`, and the cocone realizing it is the one
whose legs are division by `sⁿ`.  Every leg is an isomorphism, so
`Stacks.CategoryTheory.isColimitOfIsIso_ι` applies.

This does not by itself give the colimit clause of [Stacks, Tag 0EBN] on `X`: restriction to `U`
preserves colimits, so this says exactly that `(colim ℱ^{[n]})|_U ≅ 𝒪_U ≅ (j_*𝒪_U)|_U`, and the
clause needs in addition the behaviour of the comparison `colim ℱ^{[n]} ⟶ j_*𝒪_U` along
`X \ U`. -/
def isColimitRestrictReflexivePowerSystemCocone :
    Limits.IsColimit (restrictReflexivePowerSystemCocone F s) :=
  Stacks.CategoryTheory.isColimitOfIsIso_ι _ fun n =>
    ⟨⟨(restrictReflexivePowerUnitIso F s n).inv,
      (restrictReflexivePowerUnitIso F s n).hom_inv_id,
      (restrictReflexivePowerUnitIso F s n).inv_hom_id⟩⟩

/-- **Why the colimit clause cannot be assembled term by term.**  One is tempted to get
`colim ℱ^{[n]} ≅ j_*𝒪_U` by proving each term already recovered from `U`, i.e.
`IsIso` of the unit `ℱ^{[n]} ⟶ j_*(ℱ^{[n]}|_U)` — via [Stacks, Tag 0E9I], whose hypothesis is
depth `≥ 2` outside `U` — and then taking the colimit of isomorphisms.  This records that the
premise of that route is *too strong to be true*: if the unit is invertible at two consecutive
reflexive powers, then the transition between them is already invertible.

Indeed the restricted transition is invertible
(`isIso_restrict_reflexivePowerTransition`), hence so is its image under
`j_*j^*`, and naturality of the unit writes the transition as a composite of three
isomorphisms.  So the route would make *every* transition of `𝒪_X →ˢ ℱ →ˢ ℱ^{[2]} →ˢ ⋯`
invertible, collapsing the colimit onto its zeroth term `𝒪_X` and turning the colimit clause
into `𝒪_X ≅ j_*𝒪_U` — algebraic Hartogs across `X \ U`.  That is false exactly when there is
something to prove: by [Stacks, Tag 0EBP]
(`AlgebraicGeometry.exists_ringKrullDim_stalk_eq_one_of_maximal_irreducible_compl_locus`) every
irreducible component of `X \ U` has codimension one, so the complement is a divisor and
functions do not extend across it.  The same codimension-one count defeats the depth hypothesis
of [Stacks, Tag 0E9I] directly: at a generic point `ξ` of a component of `X \ U` the stalk
`𝒪_{X, ξ}` has Krull dimension one, so no coherent module has depth `≥ 2` there.  Consistently,
clause (3) of [Stacks, Tag 0AY6]
(`AlgebraicGeometry.isReflexive_isTorsionFree_propertyS2_extension_tfae`) obtains such a unit
isomorphism only for *some* open with codimension `≥ 2` complement, never for this `U`.

The colimit clause therefore needs the source's own argument along `X \ U`; it does not follow
from invertibility of the units at the individual terms. -/
theorem isIso_reflexivePowerTransition_of_isIso_unit (n : ℕ)
    (h₀ : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction
      (sectionIsomorphismOpen X F s).ι).unit.app (reflexivePower F n)))
    (h₁ : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction
      (sectionIsomorphismOpen X F s).ι).unit.app (reflexivePower F (n + 1)))) :
    IsIso (reflexivePowerTransition F s n) := by
  set j := (sectionIsomorphismOpen X F s).ι with hj
  have := isIso_restrict_reflexivePowerTransition F s n
  have : IsIso ((Scheme.Modules.pullback j).map (reflexivePowerTransition F s n)) := by
    have hnat := (Scheme.Modules.restrictFunctorIsoPullback j).hom.naturality
      (reflexivePowerTransition F s n)
    have h : IsIso ((Scheme.Modules.restrictFunctor j).map (reflexivePowerTransition F s n) ≫
        (Scheme.Modules.restrictFunctorIsoPullback j).hom.app (reflexivePower F (n + 1))) :=
      inferInstance
    rw [hnat] at h
    exact IsIso.of_isIso_comp_left
      ((Scheme.Modules.restrictFunctorIsoPullback j).hom.app (reflexivePower F n)) _
  have : IsIso ((Scheme.Modules.pullback j ⋙ Scheme.Modules.pushforward j).map
      (reflexivePowerTransition F s n)) := by
    dsimp only [Functor.comp_map]
    infer_instance
  have := h₀
  have := h₁
  have hnat := (Scheme.Modules.pullbackPushforwardAdjunction j).unit.naturality
    (reflexivePowerTransition F s n)
  dsimp only [Functor.id_map] at hnat
  have hcomp : IsIso (reflexivePowerTransition F s n ≫
      (Scheme.Modules.pullbackPushforwardAdjunction j).unit.app (reflexivePower F (n + 1))) := by
    rw [hnat]; infer_instance
  exact IsIso.of_isIso_comp_right _
    ((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app (reflexivePower F (n + 1)))

end Cocone

end Stacks.AlgebraicGeometry.ReflexivePowers

end

end
