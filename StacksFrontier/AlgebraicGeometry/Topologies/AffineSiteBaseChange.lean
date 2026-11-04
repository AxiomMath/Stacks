module

public import StacksFrontier.AlgebraicGeometry.Topologies.CartesianModulesSheafAnyUniverse
public import StacksFrontier.AlgebraicGeometry.Scheme.AffinePullbackGlobalSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.TerminalBaseChangePresheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.SliceAdjunctions

/-!
# Base change of modules on a site of affine schemes

Let `C` be a category with fibre products and `L : C ⥤ Scheme` a functor preserving them whose
values are affine, and give `C` the presheaf of rings `O = Γ ∘ L` of global functions.  A
topology `J` on `C` is *flatly cofinal* for `L` when every covering sieve contains a finite
covering family which `L` carries to a flat covering of schemes.  For an object `x` of `C` and a
module `N` over `O(x)`, of an arbitrary universe, the base change `V ↦ O(V) ⊗_{O(x)} N` is a
presheaf of modules on the slice `C/x`. It is cartesian, and it is the restriction along
`Over.post L` of the base-change presheaf on the slice of all schemes over `L x`.

## Main definitions

* `Stacks.AffineSiteBaseChange.rings`: the presheaf of rings `Γ ∘ L`.
* `Stacks.AffineSiteBaseChange.IsFlatCofinal`: flat cofinality of a topology.
* `Stacks.AffineSiteBaseChange.overIdTerminal`: the terminal object `id_X` of `C/X`, with the
  morphism from `Y` being `Y.hom` on the nose.
* `Stacks.AffineSiteBaseChange.bigBaseChange`: the base-change presheaf on the slice of all
  schemes over a scheme `S`.

## Main results

* `Stacks.AffineSiteBaseChange.IsFlatCofinal.over`: flat cofinality passes to slices.
* `Stacks.AffineSiteBaseChange.isIso_restrictionBaseChange_baseChangePresheaf`: the base-change
  presheaf along a terminal object is cartesian.
* `Stacks.AffineSiteBaseChange.baseChangePresheaf_presheaf_eq`: the base-change presheaf on the
  slice at `x` is the restriction of `bigBaseChange (L x)` along `Over.post L`.

## References

* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
* [Stacks Project, Tag 0H0U](https://stacks.math.columbia.edu/tag/0H0U)
* [Stacks Project, Tag 0H0X](https://stacks.math.columbia.edu/tag/0H0X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.AffineSiteBaseChange

universe t u v w

variable {C : Type v} [Category.{w} C] (L : C ⥤ AlgebraicGeometry.Scheme.{u})

open AlgebraicGeometry

/-- The presheaf of commutative rings of global regular functions of a functor to schemes. -/
abbrev rings : Cᵒᵖ ⥤ CommRingCat.{u} := L.op ⋙ Scheme.Γ

/-- A topology is *flatly cofinal* for `L` when every covering sieve contains a finite family
which generates a covering sieve and whose image under `L` is a flat covering of schemes. -/
def IsFlatCofinal (J : GrothendieckTopology C) : Prop :=
  ∀ (U : C) (S : Sieve U), S ∈ J U → ∃ E : PreZeroHypercover.{0} U, Finite E.I₀ ∧
    (E.map L).presieve₀ ∈ Scheme.precoverage @Flat (L.obj U) ∧ E.sieve₀ ≤ S ∧ E.sieve₀ ∈ J U

variable {L} in
/-- Flat cofinality passes to the slices. -/
theorem IsFlatCofinal.over {J : GrothendieckTopology C} (hJ : IsFlatCofinal L J) (x : C) :
    IsFlatCofinal (Over.forget x ⋙ L) (J.over x) := by
  intro V S hS
  obtain ⟨E, hfin, hE, hES, hEJ⟩ := hJ V.left (Sieve.overEquiv V S) hS
  let E' : PreZeroHypercover.{0} V :=
    { I₀ := E.I₀, X := fun i => Over.mk (E.f i ≫ V.hom),
      f := fun i => Over.homMk (E.f i) }
  have hsieve : Sieve.overEquiv V E'.sieve₀ = E.sieve₀ := by
    rw [PreZeroHypercover.sieve₀, Sieve.overEquiv_generate]
    refine le_antisymm ((Sieve.generate_le_iff _ _).mpr ?_) ((Sieve.generate_le_iff _ _).mpr ?_)
    · rintro W g ⟨Y, h, u, ⟨i⟩, rfl⟩
      exact E.sieve₀.downward_closed (Sieve.le_generate _ _ _ ⟨i⟩) u
    · rintro W g ⟨i⟩
      exact Sieve.le_generate _ _ _ ⟨E'.X i, E'.f i, 𝟙 _, ⟨i⟩, (Category.id_comp _).symm⟩
  refine ⟨E', hfin, hE, (Sieve.generate_le_iff _ _).mpr fun W f ⟨i⟩ => ?_, ?_⟩
  · rw [← (Sieve.overEquiv V).symm_apply_apply S]
    exact hES _ (Sieve.le_generate E.presieve₀ _ _ (Presieve.ofArrows.mk i))
  · rwa [GrothendieckTopology.mem_over_iff, hsieve]

/-! ### The base-change presheaf is cartesian -/

section Cartesian

open scoped ChangeOfRings

/-- Restriction of a base change `A ⊗_R N ⟶ B ⊗_R N`, `s ⊗ n ↦ b(s) ⊗ n`, along a factorization
`c = b ∘ a` of the structure maps has invertible adjoint transpose `B ⊗_A (A ⊗_R N) ⟶ B ⊗_R N`:
it is the inverse of the composition isomorphism of extension of scalars. -/
theorem isIso_homEquiv_symm_of_comp {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    (a : R →+* A) (b : A →+* B) (c : R →+* B) (h : b.comp a = c) (N : ModuleCat.{max t u} R)
    (φ : (ModuleCat.extendScalars a).obj N ⟶
      (ModuleCat.restrictScalars b).obj ((ModuleCat.extendScalars c).obj N))
    (hφ : ∀ (s : A) (n : N), φ (s ⊗ₜ[R,a] n) = b s ⊗ₜ[R,c] n) :
    IsIso (((ModuleCat.extendRestrictScalarsAdj b).homEquiv _ _).symm φ) := by
  subst h
  have key' : (ModuleCat.extendScalarsComp a b).hom.app N ≫
      ((ModuleCat.extendRestrictScalarsAdj b).homEquiv _ _).symm φ = 𝟙 _ := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro n
    have e := ModuleCat.extendScalarsComp_hom_app_one_tmul a b N n
    have h1 : (((ModuleCat.extendRestrictScalarsAdj b).homEquiv _ _).symm φ)
        ((1 : B) ⊗ₜ[A,b] ((1 : A) ⊗ₜ[R,a] n)) = φ ((1 : A) ⊗ₜ[R,a] n) :=
      congrArg (fun g => g ((1 : A) ⊗ₜ[R,a] n))
        (((ModuleCat.extendRestrictScalarsAdj b).homEquiv _ _).apply_symm_apply φ)
    refine (ConcreteCategory.comp_apply _ _ _).trans ?_
    refine (congrArg _ e).trans (h1.trans ((hφ 1 n).trans ?_))
    exact congrArg (· ⊗ₜ[R,b.comp a] n) (map_one b)
  have key : ((ModuleCat.extendRestrictScalarsAdj b).homEquiv _ _).symm φ =
      (ModuleCat.extendScalarsComp a b).inv.app N := by
    rw [← cancel_epi ((ModuleCat.extendScalarsComp a b).hom.app N), key', Iso.hom_inv_id_app]
  rw [key]
  infer_instance

open Stacks.TerminalBaseChange in
/-- The base-change presheaf `U ↦ O(U) ⊗_{O(X)} N` along a terminal object `X` is cartesian: its
restriction maps are base-change isomorphisms. -/
theorem isIso_restrictionBaseChange_baseChangePresheaf {D : Type*} [Category D]
    (O : Dᵒᵖ ⥤ RingCat.{u}) [CommSections O] {X₀ : D} (hX : IsTerminal X₀)
    (N : ModuleCat.{max t u} (O.obj (op X₀))) {X Y : Dᵒᵖ} (f : X ⟶ Y) :
    IsIso (Stacks.PresheafOfModules.restrictionBaseChange.{_, _, u, t} (R := commPresheaf O)
      ((baseChangePresheaf.{t} O hX).obj N) f) :=
  isIso_homEquiv_symm_of_comp (rho O hX X) (O.map f).hom (rho O hX Y)
    (rho_comp O hX f) N _ fun _ _ => rfl

end Cartesian

/-! ### Commutativity of the section rings -/

section Sheaf

open Stacks.TerminalBaseChange Stacks.Sites.OverModules

/-- The section rings of the global functions of a functor to schemes, restricted to a slice,
are commutative. -/
instance commSections_overRingPresheaf_rings (x : C) :
    CommSections (overRingPresheaf (rings L ⋙ forget₂ CommRingCat RingCat) x) :=
  ⟨fun U a b => @mul_comm (Γ(L.obj U.unop.left, ⊤)) _ a b⟩

end Sheaf

/-! ### Transport to the slice of all schemes -/

section Transport

open Stacks.TerminalBaseChange Stacks.Sites.OverModules

/-- The identity of `X` is a terminal object of the slice over `X`, with the morphism from `Y`
being `Y.hom` itself, definitionally. -/
def overIdTerminal {D : Type*} [Category D] (X : D) : IsTerminal (Over.mk (𝟙 X)) :=
  IsTerminal.ofUniqueHom (fun Y => Over.homMk Y.hom) (fun Y m => by
    ext
    simpa using Over.w m)

/-- The base-change presheaves built from two witnesses that `X₀` is terminal are isomorphic. -/
def baseChangePresheafIsoOfTerminal {D : Type*} [Category D] (O : Dᵒᵖ ⥤ RingCat.{u})
    [CommSections O] {X₀ : D} (hX hX' : IsTerminal X₀) :
    baseChangePresheaf.{t} O hX ≅ baseChangePresheaf.{t} O hX' :=
  (baseChangeAdj.{t} O hX).leftAdjointUniq (baseChangeAdj.{t} O hX')

/-- The base-change presheaf on the slice of all schemes over a scheme `S`. -/
abbrev bigBaseChange (S : Scheme.{u})
    (N : ModuleCat.{max t u}
      ((overRingPresheaf (rings (𝟭 Scheme.{u}) ⋙ forget₂ CommRingCat RingCat) S).obj
        (op (Over.mk (𝟙 S))))) :
    PresheafOfModules.{max t u}
      (overRingPresheaf (rings (𝟭 Scheme.{u}) ⋙ forget₂ CommRingCat RingCat) S) :=
  (baseChangePresheaf.{t} (overRingPresheaf (rings (𝟭 Scheme.{u}) ⋙ forget₂ CommRingCat RingCat) S)
    (overIdTerminal S)).obj N

/-- The base-change presheaf on the slice at `x` is the restriction of the base-change presheaf
on the slice of all schemes over `L x` along `Over.post L`, on the nose. -/
theorem baseChangePresheaf_presheaf_eq (x : C) (N : ModuleCat.{max t u}
      ((overRingPresheaf (rings L ⋙ forget₂ CommRingCat RingCat) x).obj
        (op (Over.mk (𝟙 x))))) :
    ((baseChangePresheaf.{t} (overRingPresheaf (rings L ⋙ forget₂ CommRingCat RingCat) x)
        (overIdTerminal x)).obj N).presheaf =
      (Over.post L).op ⋙ (bigBaseChange.{t} (L.obj x) N).presheaf := rfl

end Transport

end Stacks.AffineSiteBaseChange
