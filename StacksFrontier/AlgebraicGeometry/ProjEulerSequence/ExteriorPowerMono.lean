module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerProdSheaf
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.StalkSplitting
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The exterior powers of a stalkwise split injection, and the first arrow of the Euler sequence

Let `X` be a topological space, `O♯` a sheaf of commutative rings on it and `f : M ⟶ N` a
morphism of sheaves of `O♯`-modules. Monomorphy of `f` is a stalkwise condition, and so is
monomorphy of the induced map `⋀ᵖ f : ⋀ᵖ M ⟶ ⋀ᵖ N`; but injectivity of a linear map does not by
itself make the induced map on exterior powers injective. What does suffice is a *retraction*: if
`g ∘ f = id` then `⋀ᵖ g ∘ ⋀ᵖ f = id`, so `⋀ᵖ f` is injective. Hence a morphism of sheaves of
modules whose stalk map is a split injection at every point has monomorphic exterior powers in
every degree.

The stalk of the functorial exterior power of `f` is the exterior power of the stalk of `f`,
under the identification `(⋀ᵖ M)_x ≅ ⋀ᵖ(M_x)` of Stacks Tag 01CH.

The Euler sequence of projective space splits on every stalk
(`Stacks.AlgebraicGeometry.ProjEulerSequence.eulerStalkSplitting`), so

`0 ⟶ ⋀ᵖ Ω_{X/R} ⟶ ⋀ᵖ (𝒪_X(-1)^{⊕ (n+1)})`

is exact on the left for every `p`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjEulerSequence.eulerStalkRetraction`: the retraction of the stalk
  of the first arrow of the Euler sequence supplied by the stalk splitting, read over the stalk
  of the structure sheaf as a sheaf of *commutative* rings.

## Main results

* `SheafOfModules.exists_germ_eq_family`: a finite family of germs is a family of germs of
  sections over one common neighbourhood.
* `SheafOfModules.exteriorPowerStalkEquiv_stalkMapL_pieceMap_germ`: the stalk of `⋀ᵖ f` on the
  germ of a wedge of local sections.
* `SheafOfModules.exteriorPowerStalkEquiv_stalkMapL_pieceMap`: the stalk of the functorial
  exterior power of a morphism is the exterior power of its stalk map, under the comparison
  isomorphism of Tag 01CH in degree `p`.
* `SheafOfModules.mono_pieceMap_of_stalkMapL_retraction`: a morphism of sheaves of modules
  whose stalk map is a split injection at every point has monomorphic exterior powers.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.mono_exteriorPowerMap_eulerFirstArrow`: the
  exterior powers of the first arrow of the Euler sequence of `ℙⁿ_R` are monomorphisms.

## Implementation notes

Rewriting inside these goals, and `rcases`/`obtain` on an existential, exhausts the default
heartbeat budget while building a motive, so the proofs are chains of `Eq.trans` and `congrArg`,
and existentials are eliminated with `Exists.elim`. The degree of a homogeneous piece is `(p : ℤ)`
for `p : ℕ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf TopologicalSpace Opposite
open AlgebraicGeometry

universe u

namespace SheafOfModules

/-! ### Naturality of the stalk of an exterior power -/

section Naturality

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {M N : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  {A B : GradedAlgebra.{u, u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  (gen : M ⟶ A.piece 1) (gen' : N ⟶ B.piece 1)

/-- A finite family of germs at `x` is a family of germs of sections over one common
neighbourhood of `x`. -/
theorem exists_germ_eq_family (K : SheafOfModules.{u}
    (toRingCat (Opens.grothendieckTopology ↥X) Osharp)) (x : ↥X) (p : ℕ)
    (v : Fin p → ↑(TopCat.Presheaf.stalk K.val.presheaf x)) :
    ∃ (U : Opens ↥X) (hx : x ∈ U) (s : Fin p → K.val.obj (op U)),
      ∀ i, TopCat.Presheaf.germ K.val.presheaf U x hx (s i) = v i := by
  choose U hU s hs using fun i : Fin p => TopCat.Presheaf.exists_germ_eq K.val.presheaf (v i)
  have hW : x ∈ (⨅ i, U i : Opens ↥X) := by
    rw [← SetLike.mem_coe, Opens.coe_iInf]
    exact Set.mem_iInter.2 hU
  exact ⟨_, hW, fun i => K.val.map (homOfLE (iInf_le U i)).op (s i), fun i =>
    (TopCat.Presheaf.germ_res_apply K.val.presheaf (homOfLE (iInf_le U i)) x hW (s i)).trans
      (hs i)⟩

/-- The stalk of `⋀ᵖ f` carries the germ of `s₀ ∧ ⋯ ∧ s_{p-1}` to the wedge of the germs of the
`f sᵢ`, read through the comparison isomorphism of Tag 01CH in degree `p` on the target. -/
theorem exteriorPowerStalkEquiv_stalkMapL_pieceMap_germ
    (hA : GradedAlgebra.IsExteriorAlgebra A gen) (hB : GradedAlgebra.IsExteriorAlgebra B gen')
    (f : M ⟶ N) (p : ℕ) (x : ↥X) (U : Opens ↥X) (hx : x ∈ U)
    (s : Fin p → M.val.obj (op U)) :
    exteriorPowerStalkEquiv B gen' hB p x
        (PresheafOfModules.stalkMapL x (hA.pieceMap hB f (p : ℤ)).val
          (TopCat.Presheaf.germ (A.piece (p : ℤ)).val.presheaf U x hx
            (A.toPresheafGradedAlgebra.homogeneousProd (op U) p
              fun i => gen.val.app (op U) (s i)))) =
      exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) p
        fun i => PresheafOfModules.stalkMapL x f.val
          (TopCat.Presheaf.germ M.val.presheaf U x hx (s i)) := by
  have happ : (hA.pieceMap hB f (p : ℤ)).val.app (op U)
        (A.toPresheafGradedAlgebra.homogeneousProd (op U) p fun i => gen.val.app (op U) (s i)) =
      B.toPresheafGradedAlgebra.homogeneousProd (op U) p
        fun i => gen'.val.app (op U) (f.val.app (op U) (s i)) :=
    GradedAlgebra.UnitalHom.app_homogeneousProd_comp (hA.map hB f) f (hA.map_app_one hB f)
      (op U) p s
  refine Eq.trans (congrArg (exteriorPowerStalkEquiv B gen' hB p x)
    (PresheafOfModules.stalkMapL_germ x (hA.pieceMap hB f (p : ℤ)).val U hx
      (A.toPresheafGradedAlgebra.homogeneousProd (op U) p
        fun i => gen.val.app (op U) (s i)))) ?_
  refine Eq.trans (congrArg (fun y => exteriorPowerStalkEquiv B gen' hB p x
    (TopCat.Presheaf.germ (B.piece (p : ℤ)).val.presheaf U x hx y)) happ) ?_
  refine Eq.trans (exteriorPowerStalkEquiv_germ_homogeneousProd B gen' hB p x U hx
    fun i => f.val.app (op U) (s i)) ?_
  exact congrArg (exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) p)
    (funext fun i => (PresheafOfModules.stalkMapL_germ x f.val U hx (s i)).symm)

/-- The stalk of the functorial exterior power of a morphism is the exterior power of its stalk
map, in the form read on the inverse of the comparison of Tag 01CH on the source. -/
theorem exteriorPowerStalkEquiv_stalkMapL_pieceMap_symm
    (hA : GradedAlgebra.IsExteriorAlgebra A gen) (hB : GradedAlgebra.IsExteriorAlgebra B gen')
    (f : M ⟶ N) (p : ℕ) (x : ↥X)
    (w : ⋀[↑(TopCat.Presheaf.stalk Osharp.obj x)]^p ↑(TopCat.Presheaf.stalk M.val.presheaf x)) :
    exteriorPowerStalkEquiv B gen' hB p x
        (PresheafOfModules.stalkMapL x (hA.pieceMap hB f (p : ℤ)).val
          ((exteriorPowerStalkEquiv A gen hA p x).symm w)) =
      exteriorPower.map p (PresheafOfModules.stalkMapL x f.val) w := by
  have hgen : ∀ v : Fin p → ↑(TopCat.Presheaf.stalk M.val.presheaf x),
      exteriorPowerStalkEquiv B gen' hB p x
          (PresheafOfModules.stalkMapL x (hA.pieceMap hB f (p : ℤ)).val
            ((exteriorPowerStalkEquiv A gen hA p x).symm
              (exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) p v))) =
        exteriorPower.map p (PresheafOfModules.stalkMapL x f.val)
          (exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) p v) := by
    intro v
    refine (exists_germ_eq_family M x p v).elim fun U h1 => h1.elim fun hx h2 =>
      h2.elim fun s hs => ?_
    have hv : v = fun i => TopCat.Presheaf.germ M.val.presheaf U x hx (s i) :=
      funext fun i => (hs i).symm
    subst hv
    have hsymm : (exteriorPowerStalkEquiv A gen hA p x).symm
          (exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) p
            fun i => TopCat.Presheaf.germ M.val.presheaf U x hx (s i)) =
        TopCat.Presheaf.germ (A.piece (p : ℤ)).val.presheaf U x hx
          (A.toPresheafGradedAlgebra.homogeneousProd (op U) p
            fun i => gen.val.app (op U) (s i)) :=
      (LinearEquiv.symm_apply_eq _).2
        (exteriorPowerStalkEquiv_germ_homogeneousProd A gen hA p x U hx s).symm
    refine Eq.trans (congrArg (fun y => exteriorPowerStalkEquiv B gen' hB p x
      (PresheafOfModules.stalkMapL x (hA.pieceMap hB f (p : ℤ)).val y)) hsymm) ?_
    refine Eq.trans (exteriorPowerStalkEquiv_stalkMapL_pieceMap_germ gen gen' hA hB f p x U hx s)
      ?_
    exact (exteriorPower.map_apply_ιMulti (PresheafOfModules.stalkMapL x f.val)
      (fun i => TopCat.Presheaf.germ M.val.presheaf U x hx (s i))).symm
  have hL : (exteriorPowerStalkEquiv B gen' hB p x).toLinearMap ∘ₗ
        (PresheafOfModules.stalkMapL x (hA.pieceMap hB f (p : ℤ)).val ∘ₗ
          (exteriorPowerStalkEquiv A gen hA p x).symm.toLinearMap) =
      exteriorPower.map p (PresheafOfModules.stalkMapL x f.val) :=
    LinearMap.ext_on_range (exteriorPower.ιMulti_span _ p _) hgen
  exact DFunLike.congr_fun hL w

/-- The stalk of the functorial exterior power of a morphism is the exterior power of its stalk
map: the comparison isomorphism `(⋀ᵖ M)_x ≅ ⋀ᵖ(M_x)` of Tag 01CH in degree `p` is natural in the
module. -/
theorem exteriorPowerStalkEquiv_stalkMapL_pieceMap
    (hA : GradedAlgebra.IsExteriorAlgebra A gen) (hB : GradedAlgebra.IsExteriorAlgebra B gen')
    (f : M ⟶ N) (p : ℕ) (x : ↥X)
    (z : ↑(TopCat.Presheaf.stalk (A.piece (p : ℤ)).val.presheaf x)) :
    exteriorPowerStalkEquiv B gen' hB p x
        (PresheafOfModules.stalkMapL x (hA.pieceMap hB f (p : ℤ)).val z) =
      exteriorPower.map p (PresheafOfModules.stalkMapL x f.val)
        (exteriorPowerStalkEquiv A gen hA p x z) :=
  (congrArg (fun y => exteriorPowerStalkEquiv B gen' hB p x
      (PresheafOfModules.stalkMapL x (hA.pieceMap hB f (p : ℤ)).val y))
    ((exteriorPowerStalkEquiv A gen hA p x).symm_apply_apply z).symm).trans
    (exteriorPowerStalkEquiv_stalkMapL_pieceMap_symm gen gen' hA hB f p x _)

/-- A morphism of sheaves of modules whose stalk map is a split injection at every point has
monomorphic exterior powers. -/
theorem mono_pieceMap_of_stalkMapL_retraction
    (hA : GradedAlgebra.IsExteriorAlgebra A gen) (hB : GradedAlgebra.IsExteriorAlgebra B gen')
    (f : M ⟶ N) (p : ℕ)
    (hf : ∀ x : ↥X, ∃ r : ↑(TopCat.Presheaf.stalk N.val.presheaf x)
        →ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)] ↑(TopCat.Presheaf.stalk M.val.presheaf x),
      r ∘ₗ PresheafOfModules.stalkMapL x f.val = LinearMap.id) :
    Mono (hA.pieceMap hB f (p : ℤ)) := by
  rw [AlgebraicGeometry.SheafOfModules.mono_iff_injective_stalkMap]
  intro x z z' hzz'
  refine (hf x).elim fun r hr => ?_
  have hstalk : PresheafOfModules.stalkMapL x (hA.pieceMap hB f (p : ℤ)).val z =
      PresheafOfModules.stalkMapL x (hA.pieceMap hB f (p : ℤ)).val z' :=
    ((stalkMap_hom_eq_stalkMapL x (hA.pieceMap hB f (p : ℤ)) z).symm.trans hzz').trans
      (stalkMap_hom_eq_stalkMapL x (hA.pieceMap hB f (p : ℤ)) z')
  exact (exteriorPowerStalkEquiv A gen hA p x).injective <|
    exteriorPower.map_injective (n := p) r hr
      (((exteriorPowerStalkEquiv_stalkMapL_pieceMap gen gen' hA hB f p x z).symm.trans
        (congrArg (exteriorPowerStalkEquiv B gen' hB p x) hstalk)).trans
        (exteriorPowerStalkEquiv_stalkMapL_pieceMap gen gen' hA hB f p x z'))

end Naturality

end SheafOfModules

namespace Stacks.AlgebraicGeometry.ProjEulerSequence

/-! ### The first arrow of the Euler sequence of projective space -/

section Euler

open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.ProjTrivialization
open AlgebraicGeometry.ProjectiveSpectrum.Proj

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] (n : ℕ)

/-- The retraction of the stalk of the first arrow of the Euler sequence carried by the stalk
splitting `eulerStalkSplitting`, as a linear map over the stalk of the structure sheaf as a sheaf
of commutative rings. -/
def eulerStalkRetraction (x : ProjectiveSpectrum.top (polyGrading R n)) :
    ↑(TopCat.Presheaf.stalk (twistMinusOneSum R n).val.presheaf x)
      →ₗ[↑(TopCat.Presheaf.stalk
        (ProjectiveSpectrum.Proj.structureSheaf (polyGrading R n)).obj x)]
      ↑(TopCat.Presheaf.stalk (projDifferentials R n).val.presheaf x) :=
  stalkCommLinearOfRingLinear x (M := (twistMinusOneSum R n).val)
    (N := (projDifferentials R n).val) (eulerStalkSplitting R n x).r.hom

/-- `eulerStalkRetraction` is a left inverse of the stalk of the first arrow of the Euler
sequence. -/
theorem eulerStalkRetraction_comp_stalkMapL
    (x : ProjectiveSpectrum.top (polyGrading R n)) :
    eulerStalkRetraction R n x ∘ₗ
        PresheafOfModules.stalkMapL x (eulerFirstArrow R n).val = LinearMap.id :=
  LinearMap.ext fun z =>
    congrArg (fun φ : _ ⟶ _ => ModuleCat.Hom.hom φ z) (eulerStalkSplitting R n x).f_r

/-- The exterior powers of the first arrow of the Euler sequence of `ℙⁿ_R` are monomorphisms:
`0 ⟶ ⋀ᵖ Ω_{X/R} ⟶ ⋀ᵖ (𝒪_X(-1)^{⊕ (n+1)})` is exact on the left for every `p`. -/
@[sga "7 XI 1.1" "(1.1.8) at twist n=0"]
theorem mono_exteriorPowerMap_eulerFirstArrow (p : ℕ) :
    Mono (Scheme.Modules.exteriorPowerMap
      (X := AlgebraicGeometry.Proj (polyGrading R n)) (eulerFirstArrow R n) (p : ℤ)) :=
  SheafOfModules.mono_pieceMap_of_stalkMapL_retraction
    (Osharp := ProjectiveSpectrum.Proj.structureSheaf (polyGrading R n))
    (Scheme.Modules.exteriorGenerator (X := AlgebraicGeometry.Proj (polyGrading R n))
      (projDifferentials R n))
    (Scheme.Modules.exteriorGenerator (X := AlgebraicGeometry.Proj (polyGrading R n))
      (twistMinusOneSum R n))
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra
      (X := AlgebraicGeometry.Proj (polyGrading R n)) (projDifferentials R n))
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra
      (X := AlgebraicGeometry.Proj (polyGrading R n)) (twistMinusOneSum R n))
    (eulerFirstArrow R n) p
    fun x => ⟨eulerStalkRetraction R n x, eulerStalkRetraction_comp_stalkMapL R n x⟩

end Euler

end Stacks.AlgebraicGeometry.ProjEulerSequence

end
