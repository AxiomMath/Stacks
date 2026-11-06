module

public import StacksFrontier.Deformation.RingedSpaceThickening.SolutionIsomorphism
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkFreeCover
public import StacksFrontier.Topology.Sheaves.RingedSpace.ThickeningTrivialization
public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalSequence
public import StacksFrontier.CategoryTheory.Sites.Modules.DifferentialsSheafification
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.Comorphism
public import StacksFrontier.Cotangent.SheavesOfRings.RingedSpaceExt
import StacksCore.Tactic.StacksAttribute

/-!
# The automorphisms of a solution of a deformation problem of ringed spaces (Stacks 08UZ (3))

Fix a first order thickening `t : (S, 𝒪_S) ⟶ (S', 𝒪_{S'})` of ringed spaces with ideal
`𝒥 = Ker(t^♯)`, a morphism `f : (X, 𝒪_X) ⟶ (S, 𝒪_S)`, an `𝒪_X`-module `𝒢` and an `f`-map
`c : 𝒥 ⟶ 𝒢`. A *solution* of the deformation problem (08UY) is a
`AlgebraicGeometry.RingedSpaceThickening.DeformationSolution t ht f G c`: a first order
thickening `i : X ⟶ X'` with ideal identified with `𝒢`, over `t`, inducing `c`.

Let `Q` be a solution. An endomorphism of `Q` fitting into (08UY) is a
`AlgebraicGeometry.RingedSpaceThickening.SolutionHom Q Q`, and by
`AlgebraicGeometry.RingedSpaceThickening.SolutionHom.isIso_hom` every such endomorphism is
already invertible, so these are exactly the automorphisms of `X'` in the diagram. This file
identifies them with `Ext⁰_{𝒪_X}(L_{X/S}, 𝒢)`, which is clause (3) of **Stacks 08UZ**.

## Main definitions

* `...SolutionHom.diff`: the section of `𝒢` by which an endomorphism of a solution moves a
  section of `𝒪_{X'}`; it is a derivation of `𝒪_{X'}` vanishing on `𝒢`.
* `...SolutionHom.toDerivation`: that derivation, descended to a relative derivation of `𝒪_X`
  over `f⁻¹𝒪_S` with values in `𝒢`.
* `...DeformationSolution.derivationSolutionHom`: conversely, the endomorphism
  `x ↦ x + δ(x mod 𝒢)` of a solution attached to a relative derivation `δ` of `𝒪_X`.
* `...DeformationSolution.thickenedPresheaf` and `...DeformationSolution.thickenedReduction`:
  `𝒪_{X'}` and the reduction `𝒪_{X'} ⟶ 𝒪_X`, read on the site of open subsets of `X` through
  the homeomorphism underlying the thickening.

## Main results

* `...SolutionHom.existsUnique_intermediateDerivation`: **the descent.** The difference
  derivation of an endomorphism of a solution descends to `𝒪_X` in exactly one way.
* `...DeformationSolution.solutionHomEquivSDerivation`: the endomorphisms of a solution are the
  relative derivations of `𝒪_X` over `f⁻¹𝒪_S` with values in `𝒢`.
* `...DeformationSolution.solutionHomEquivCotangentExt`: **Stacks 08UZ, clause (3).** Those
  derivations are `Ext⁰_{𝒪_X}(L_{X/S}, 𝒢)`.

## Implementation notes

The source deduces clause (3) from Deformation Theory, Lemma 08UC through the identifications
`NL_{X/S} = τ_{≥-1}L_{X/S}` and `H⁰(L_{X/S}) = Ω_{X/S}`. The route here is the direct one: an
endomorphism of a solution is `x ↦ x + δ(x)` for a unique relative derivation `δ`, and
`Ext⁰_{𝒪_X}(L_{X/S}, 𝒢) = Hom_{𝒪_X}(Ω_{X/S}, 𝒢) = Der_{f⁻¹𝒪_S}(𝒪_X, 𝒢)` by
`Stacks.Sheaves.RingedSpaceCotangent.extZeroCotangentAddEquiv` (Stacks 08UV and the
`t`-structure computation of Stacks 06XS) and the corepresentability of relative derivations
(Stacks 04BL). Clauses (1) and (2) of the tag are about `Ext²` and `Ext¹` and are not touched.

The substance is the **descent**: the difference `x ↦ e^♯(x) - x` is a derivation of the
*thickened* structure sheaf `𝒪_{X'}`, and the reduction `𝒪_{X'} ⟶ i_*𝒪_X` is only locally
surjective, so the derivation of `𝒪_X` it induces cannot be written down on sections. It is
obtained from `AlgebraicGeometry.SheafOfModules.existsUnique_derivation_extension` applied to
the sectionwise quotient `Stacks.Sites.Conormal.quotientToTarget` of `𝒪_{X'}` by the kernel of
the reduction, which is locally bijective; the difference derivation kills that kernel exactly
because an endomorphism of a solution is the identity on `𝒢`.

Both the derivation and the reduction have to be read on one site. The derivation of `𝒪_X`
lives on the opens of `X` and `𝒪_{X'}` on the opens of `X'`, so `𝒪_{X'}` is transported along
the homeomorphism `i.base`: `thickenedPresheaf` is its pushforward along the inverse
homeomorphism, whose sections over an open of `X` are honest sections of `𝒪_{X'}`. Local
surjectivity survives the transport because `Opens.map` of the inverse homeomorphism is
cocontinuous (`coverPreserving_opensMap` and `isCocontinuous_opensEquiv`), and
`CategoryTheory.Presheaf.isLocallySurjective_whisker` then applies.

That the descended derivation is a derivation *over `f⁻¹𝒪_S`* is the one place where the base
thickening is used: a section of `𝒪_S` lifts, near each point, to a section of `𝒪_{S'}` because
`t` is a thickening, and on the image of `f'^♯` the difference derivation vanishes because an
endomorphism of a solution is a morphism over `S'`. The conclusion is then transported from
single sections of `𝒪_S` to all of `f⁻¹𝒪_S` by
`Stacks.Sheaves.RingedSpaceDifferentials.derivation_d_inverseImageStructureMap_eq_zero`.

## References

* [Stacks Project, Tag 08UZ](https://stacks.math.columbia.edu/tag/08UZ)
* [Stacks Project, Tag 08UY](https://stacks.math.columbia.edu/tag/08UY), the deformation problem
* [Stacks Project, Tag 08UV](https://stacks.math.columbia.edu/tag/08UV), `H⁰(L_{X/S}) = Ω_{X/S}`
* [Stacks Project, Tag 04BL](https://stacks.math.columbia.edu/tag/04BL), corepresentability of
  relative derivations
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

variable {X S S' : RingedSpace.{u, u}} {t : S ⟶ S'}
  {ht : IsFirstOrderThickening t} {f : X ⟶ S}
  {G : SheafOfModules.{u} (structureSheafRing X)}
  {c : (modulePullback f).obj
    ((modulePullback t).obj (AlgebraicGeometry.SheafOfModules.idealSheaf t)) ⟶ G}

namespace DeformationSolution

variable (Q : DeformationSolution t ht f G c)

/-- The section of the thickened structure sheaf attached to a section of the prescribed
module. -/
noncomputable def incl {U : (Opens Q.X'.carrier)ᵒᵖ}
    (g : ((modulePushforward Q.i).obj G).val.obj U) : Q.X'.presheaf.obj U :=
  (Q.idealInclusion.val.app U).hom g

/-- The reduction of a section of the thickened structure sheaf. -/
noncomputable abbrev reduction {U : (Opens Q.X'.carrier)ᵒᵖ} (x : Q.X'.presheaf.obj U) :
    ((modulePushforward Q.i).obj (SheafOfModules.unit (structureSheafRing X))).val.obj U :=
  (Q.structureMap.val.app U).hom x

/-- The inclusion of the prescribed module is injective on sections. -/
theorem incl_injective {U : (Opens Q.X'.carrier)ᵒᵖ} :
    Function.Injective (Q.incl (U := U)) := by
  have hm : Mono Q.idealInclusion := by
    have : IsIso Q.idealIso.hom := inferInstance
    exact mono_comp _ _
  have : Mono ((SheafOfModules.evaluation (structureSheafRing Q.X') U).map Q.idealInclusion) :=
    inferInstance
  exact (ModuleCat.mono_iff_injective _).mp this

/-- A section of the prescribed module is killed by the reduction. -/
theorem reduction_incl {U : (Opens Q.X'.carrier)ᵒᵖ}
    (g : ((modulePushforward Q.i).obj G).val.obj U) : Q.reduction (Q.incl g) = 0 :=
  congrArg (fun k : (modulePushforward Q.i).obj G ⟶
    (modulePushforward Q.i).obj (SheafOfModules.unit (structureSheafRing X)) =>
      (k.val.app U).hom g) Q.idealInclusion_comp_structureMap

/-- Every section killed by the reduction comes from a section of the prescribed module. -/
theorem exists_incl {U : (Opens Q.X'.carrier)ᵒᵖ} (x : Q.X'.presheaf.obj U)
    (hx : Q.reduction x = 0) :
    ∃ g : ((modulePushforward Q.i).obj G).val.obj U, Q.incl g = x := by
  obtain ⟨w, hw⟩ := Stacks.SheafOfModules.exists_kernel_section Q.structureMap U x hx
  refine ⟨(Q.idealIso.inv.val.app U).hom w, ?_⟩
  have h : (Q.idealIso.inv ≫ Q.idealInclusion).val.app U = (kernel.ι Q.structureMap).val.app U :=
    congrArg (fun k : kernel Q.structureMap ⟶ SheafOfModules.unit (structureSheafRing Q.X') =>
      k.val.app U) Q.idealIso_inv_comp_idealInclusion
  exact (congrArg (fun k => (ConcreteCategory.hom k) w) h).trans hw

variable {Q}

/-- The inclusion of the prescribed module sends the zero section to the zero section. -/
@[simp]
theorem incl_zero {U : (Opens Q.X'.carrier)ᵒᵖ} :
    Q.incl (0 : ((modulePushforward Q.i).obj G).val.obj U) = 0 :=
  map_zero (Q.idealInclusion.val.app U).hom

/-- The inclusion of the prescribed module is additive on sections. -/
theorem incl_add {U : (Opens Q.X'.carrier)ᵒᵖ}
    (g h : ((modulePushforward Q.i).obj G).val.obj U) :
    Q.incl (g + h) = Q.incl g + Q.incl h :=
  map_add (Q.idealInclusion.val.app U).hom g h

/-- The inclusion of the prescribed module commutes with differences of sections. -/
theorem incl_sub {U : (Opens Q.X'.carrier)ᵒᵖ}
    (g h : ((modulePushforward Q.i).obj G).val.obj U) :
    Q.incl (g - h) = Q.incl g - Q.incl h :=
  map_sub (Q.idealInclusion.val.app U).hom g h

/-- The inclusion of the prescribed module commutes with the restriction maps of the site. -/
theorem incl_naturality {U V : (Opens Q.X'.carrier)ᵒᵖ} (k : U ⟶ V)
    (g : ((modulePushforward Q.i).obj G).val.obj U) :
    Q.incl (((modulePushforward Q.i).obj G).val.map k g) =
      (Q.X'.presheaf.map k).hom (Q.incl g) :=
  PresheafOfModules.naturality_apply Q.idealInclusion.val k g

/-- Multiplying a section of the ideal by a section of the thickened structure sheaf is the
module action of that section. -/
theorem mul_incl {U : (Opens Q.X'.carrier)ᵒᵖ} (x : Q.X'.presheaf.obj U)
    (g : ((modulePushforward Q.i).obj G).val.obj U) :
    x * Q.incl g = Q.incl (x • g) :=
  ((Q.idealInclusion.val.app U).hom.map_smul x g).symm

/-- The reduction commutes with differences of sections. -/
theorem reduction_sub {U : (Opens Q.X'.carrier)ᵒᵖ} (x y : Q.X'.presheaf.obj U) :
    Q.reduction (x - y) = Q.reduction x - Q.reduction y :=
  map_sub (Q.structureMap.val.app U).hom x y

/-- The ideal of a solution has square zero: the product of two of its sections vanishes. -/
theorem incl_mul_incl {U : (Opens Q.X'.carrier)ᵒᵖ}
    (g h : ((modulePushforward Q.i).obj G).val.obj U) : Q.incl g * Q.incl h = 0 := by
  set I := RingHom.ker ((structureSheafHom Q.i).hom.app U).hom
  have hmem : Q.incl g * Q.incl h ∈ I * I :=
    Ideal.mul_mem_mul (RingHom.mem_ker.2 (Q.reduction_incl g))
      (RingHom.mem_ker.2 (Q.reduction_incl h))
  have hmulI : I * I = ⊥ := by
    have hp : I ^ 2 = ⊥ := Q.i_firstOrder.2 U.unop
    rw [show (2 : ℕ) = 1 + 1 from rfl, Submodule.pow_succ, Submodule.pow_one] at hp
    exact hp
  rw [hmulI] at hmem
  simpa using hmem

end DeformationSolution

namespace SolutionHom

variable {Q : DeformationSolution t ht f G c} (e : SolutionHom Q Q)

/-- A self-map of the thickened space under `X` is the identity on the underlying space. -/
private theorem base_eq_id_of_comp_eq {g : Q.X' ⟶ Q.X'} (h : Q.i ≫ g = Q.i) :
    g.hom.base = 𝟙 Q.X'.carrier := by
  have : IsIso Q.i.hom.base := Q.i_firstOrder.1.1
  refine (cancel_epi Q.i.hom.base).1 ?_
  rw [Category.comp_id]
  exact congrArg (fun k : X ⟶ Q.X' => k.hom.base) h

/-- An endomorphism of a solution is the identity on the underlying space: it is a factor of
the identity along the epimorphism underlying the thickening. -/
theorem base_eq_id : e.hom.hom.base = 𝟙 Q.X'.carrier :=
  base_eq_id_of_comp_eq e.thickening_comm

/-- Pushing the thickened structure sheaf forward along an endomorphism of a solution returns
it unchanged. -/
theorem pushforward_presheaf_eq :
    (TopCat.Presheaf.pushforward CommRingCat e.hom.hom.base).obj Q.X'.presheaf =
      Q.X'.presheaf := by
  rw [e.base_eq_id]; rfl

/-- The comorphism of an endomorphism of a solution, read as an endomorphism of the thickened
structure sheaf. The underlying space being untouched, the target of the comorphism is the
structure sheaf itself. -/
noncomputable def selfComorphism : Q.X'.presheaf ⟶ Q.X'.presheaf :=
  e.hom.hom.c ≫ eqToHom e.pushforward_presheaf_eq

/-- An endomorphism of a solution is the identity on the underlying space and its comorphism on
the structure sheaf. -/
private theorem hom_eq_mk : e.hom = ⟨⟨𝟙 Q.X'.carrier, e.selfComorphism⟩⟩ := by
  obtain ⟨⟨⟨eb, ec⟩⟩, h1, h2, h3⟩ := e
  have hb : eb = 𝟙 Q.X'.carrier := base_eq_id_of_comp_eq h1
  subst hb
  exact congrArg (fun k => (⟨⟨𝟙 Q.X'.carrier, k⟩⟩ : Q.X' ⟶ Q.X')) (Category.comp_id ec).symm

/-- An endomorphism of a solution is the identity after reducing to `X`: it is a morphism
under `X`. -/
theorem selfComorphism_comp : e.selfComorphism ≫ Q.i.hom.c = Q.i.hom.c := by
  have h1 := e.thickening_comm
  rw [e.hom_eq_mk] at h1
  ext U x
  have h := SheafedSpace.congr_hom_app h1 (op U)
  simp only [SheafedSpace.comp_hom_c_app, eqToHom_map] at h
  exact congrArg (fun k => (ConcreteCategory.hom k) x) h

/-- An endomorphism of a solution leaves the image of the thickened base untouched: it is a
morphism over `S'`. -/
theorem selfComorphism_baseMap :
    Q.f'.hom.c ≫ (TopCat.Presheaf.pushforward CommRingCat Q.f'.hom.base).map e.selfComorphism =
      Q.f'.hom.c := by
  have h2 := e.base_comm
  rw [e.hom_eq_mk] at h2
  ext W x
  have h := SheafedSpace.congr_hom_app h2 (op W)
  simp only [SheafedSpace.comp_hom_c_app, eqToHom_map] at h
  exact congrArg (fun k => (ConcreteCategory.hom k) x) h

/-- The reduction of a solution is the comorphism of its thickening, on sections. -/
theorem reduction_eq (U : (Opens Q.X'.carrier)ᵒᵖ) (x : Q.X'.presheaf.obj U) :
    Q.reduction x = (Q.i.hom.c.app U).hom x := rfl

/-- An endomorphism of a solution does not change the reduction of a section. -/
theorem reduction_selfComorphism (U : (Opens Q.X'.carrier)ᵒᵖ) (x : Q.X'.presheaf.obj U) :
    Q.reduction ((e.selfComorphism.app U).hom x) = Q.reduction x :=
  congrArg (fun k => (ConcreteCategory.hom k) x) (congrArg (fun k => k.app U)
    e.selfComorphism_comp)

/-- An `eqToIso` between pushforward functors acts as the identity on sections: its components
are casts along an equality of objects whose sections are the same. -/
private theorem eqToIso_hom_app_val_app_heq {Y Z : RingedSpace.{u, u}}
    {F₁ F₂ : SheafOfModules.{u} (structureSheafRing Y) ⥤
      SheafOfModules.{u} (structureSheafRing Z)}
    (hF : F₁ = F₂) (M : SheafOfModules.{u} (structureSheafRing Y))
    (U : (Opens Z.carrier)ᵒᵖ) (g : (F₁.obj M).val.obj U) :
    HEq ((((eqToIso hF).hom.app M).val.app U).hom g) g := by
  subst hF
  simp

/-- An endomorphism of a solution is the identity on the prescribed ideal. This is the third
defining condition of a morphism of solutions, read on sections. -/
theorem selfComorphism_incl (U : (Opens Q.X'.carrier)ᵒᵖ)
    (g : ((modulePushforward Q.i).obj G).val.obj U) :
    (e.selfComorphism.app U).hom (Q.incl g) = Q.incl g := by
  obtain ⟨⟨⟨eb, ec⟩⟩, h1, h2, h3⟩ := e
  have hb : eb = 𝟙 Q.X'.carrier := base_eq_id_of_comp_eq h1
  subst hb
  have hF : modulePushforward Q.i
      = modulePushforward (Q.i ≫ (⟨⟨𝟙 _, ec⟩⟩ : Q.X' ⟶ Q.X')) :=
    (congrArg (fun k : X ⟶ Q.X' => modulePushforward k) h1).symm
  have hP : (pushforwardIsoOfComp Q.i (⟨⟨𝟙 _, ec⟩⟩ : Q.X' ⟶ Q.X') Q.i h1).hom.app G
      = (eqToIso hF).hom.app G := by
    simp only [pushforwardIsoOfComp, Iso.trans_hom, NatTrans.comp_app,
      modulePushforwardCompSymm, Iso.symm_hom, modulePushforwardComp_inv_app]
    exact Category.comp_id _
  have hcast : (((eqToIso hF).hom.app G).val.app U).hom g = g :=
    eq_of_heq (eqToIso_hom_app_val_app_heq hF G U g)
  have h := congrArg (fun k => (k.val.app U).hom g) h3
  rw [hP] at h
  refine Eq.trans (congrArg (fun k : Q.X'.presheaf ⟶ Q.X'.presheaf =>
    (ConcreteCategory.hom (k.app U)) (Q.incl g)) (Category.comp_id ec)) (h.trans ?_)
  exact congrArg (fun z : ((modulePushforward Q.i).obj G).val.obj U => Q.incl z) hcast

/-! ### The derivation attached to an endomorphism of a solution -/

/-- An endomorphism of a solution moves a section of the thickened structure sheaf by a section
of the prescribed module. -/
theorem exists_diff (U : (Opens Q.X'.carrier)ᵒᵖ) (x : Q.X'.presheaf.obj U) :
    ∃ g : ((modulePushforward Q.i).obj G).val.obj U,
      Q.incl g = (e.selfComorphism.app U).hom x - x :=
  Q.exists_incl _ (by
    rw [DeformationSolution.reduction_sub, e.reduction_selfComorphism, sub_self])

/-- The section of the prescribed module by which an endomorphism of a solution moves a section
of the thickened structure sheaf. -/
noncomputable def diff (U : (Opens Q.X'.carrier)ᵒᵖ) (x : Q.X'.presheaf.obj U) :
    ((modulePushforward Q.i).obj G).val.obj U :=
  (e.exists_diff U x).choose

/-- The defining property of `SolutionHom.diff`. -/
theorem incl_diff (U : (Opens Q.X'.carrier)ᵒᵖ) (x : Q.X'.presheaf.obj U) :
    Q.incl (e.diff U x) = (e.selfComorphism.app U).hom x - x :=
  (e.exists_diff U x).choose_spec

/-- The difference of an endomorphism of a solution and the identity vanishes on the sections
that the endomorphism fixes. -/
private theorem diff_eq_zero_of_apply_eq {U : (Opens Q.X'.carrier)ᵒᵖ} {x : Q.X'.presheaf.obj U}
    (hx : (e.selfComorphism.app U).hom x = x) : e.diff U x = 0 := by
  refine Q.incl_injective ?_
  rw [e.incl_diff, hx, sub_self, DeformationSolution.incl_zero]

/-- The difference of an endomorphism of a solution and the identity is additive. -/
theorem diff_add (U : (Opens Q.X'.carrier)ᵒᵖ) (x y : Q.X'.presheaf.obj U) :
    e.diff U (x + y) = e.diff U x + e.diff U y := by
  refine Q.incl_injective ?_
  rw [DeformationSolution.incl_add, e.incl_diff, e.incl_diff, e.incl_diff, map_add]
  abel

/-- The difference of an endomorphism of a solution and the identity commutes with the
restriction maps of the site. -/
theorem diff_naturality {U V : (Opens Q.X'.carrier)ᵒᵖ} (k : U ⟶ V)
    (x : Q.X'.presheaf.obj U) :
    e.diff V ((Q.X'.presheaf.map k).hom x) =
      ((modulePushforward Q.i).obj G).val.map k (e.diff U x) := by
  refine Q.incl_injective ?_
  have hn := congrArg (fun z => (ConcreteCategory.hom z) x) (e.selfComorphism.naturality k)
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at hn
  rw [DeformationSolution.incl_naturality, e.incl_diff, e.incl_diff, map_sub]
  exact congrArg (fun z => z - (Q.X'.presheaf.map k).hom x) hn

/-- The Leibniz rule for the difference of an endomorphism of a solution and the identity: the
scalars act through the reduction, which is how the prescribed module is an
`𝒪_{X'}`-module. -/
theorem diff_mul (U : (Opens Q.X'.carrier)ᵒᵖ) (x y : Q.X'.presheaf.obj U) :
    e.diff U (x * y) = x • e.diff U y + y • e.diff U x := by
  refine Q.incl_injective ?_
  have hx : (e.selfComorphism.app U).hom x = x + Q.incl (e.diff U x) := by
    rw [e.incl_diff]; abel
  have hy : (e.selfComorphism.app U).hom y = y + Q.incl (e.diff U y) := by
    rw [e.incl_diff]; abel
  have h0 : Q.incl (e.diff U x) * Q.incl (e.diff U y) = 0 :=
    DeformationSolution.incl_mul_incl _ _
  rw [DeformationSolution.incl_add, ← DeformationSolution.mul_incl,
    ← DeformationSolution.mul_incl, e.incl_diff, map_mul, hx, hy]
  linear_combination h0

/-- The difference of an endomorphism of a solution and the identity vanishes on the prescribed
ideal; this is what lets it descend to `𝒪_X`. -/
theorem diff_incl (U : (Opens Q.X'.carrier)ᵒᵖ)
    (g : ((modulePushforward Q.i).obj G).val.obj U) : e.diff U (Q.incl g) = 0 :=
  e.diff_eq_zero_of_apply_eq (e.selfComorphism_incl U g)

/-- `SolutionHom.selfComorphism_baseMap`, on sections. -/
theorem selfComorphism_baseMap_apply (W : (Opens S'.carrier)ᵒᵖ) (s : S'.presheaf.obj W) :
    (e.selfComorphism.app ((Opens.map Q.f'.hom.base).op.obj W)).hom
        ((Q.f'.hom.c.app W).hom s) = (Q.f'.hom.c.app W).hom s :=
  congrArg (fun k => (ConcreteCategory.hom k) s)
    (congrArg (fun k => k.app W) e.selfComorphism_baseMap)

/-- An endomorphism of a solution moves no section pulled back from the thickened base: it is a
morphism over `S'`. -/
theorem diff_baseMap (W : (Opens S'.carrier)ᵒᵖ) (s : S'.presheaf.obj W) :
    e.diff ((Opens.map Q.f'.hom.base).op.obj W) ((Q.f'.hom.c.app W).hom s) = 0 :=
  e.diff_eq_zero_of_apply_eq (e.selfComorphism_baseMap_apply W s)

/-- The difference of an endomorphism of a solution and the identity kills the unit section. -/
theorem diff_one (U : (Opens Q.X'.carrier)ᵒᵖ) : e.diff U 1 = 0 :=
  e.diff_eq_zero_of_apply_eq (map_one _)

end SolutionHom

/-! ### Reading the thickened structure sheaf on the site of opens of `X` -/

namespace DeformationSolution

variable (Q : DeformationSolution t ht f G c)

/-- The homeomorphism of underlying spaces given by the thickening of a solution. -/
noncomputable def baseIso : X.carrier ≅ Q.X'.carrier :=
  haveI : IsIso Q.i.hom.base := Q.i_firstOrder.1.1
  asIso Q.i.hom.base

/-- The homeomorphism of a solution is the underlying map of its thickening. -/
theorem baseIso_hom : Q.baseIso.hom = Q.i.hom.base := rfl

/-- The induced equivalence of the two sites of open subsets. -/
noncomputable def opensEquiv : Opens X.carrier ≌ Opens Q.X'.carrier :=
  (Opens.mapMapIso Q.baseIso).symm

/-- The site equivalence of a solution takes preimages along the inverse homeomorphism. -/
theorem opensEquiv_functor : Q.opensEquiv.functor = Opens.map Q.baseIso.inv := rfl

/-- The inverse of the site equivalence of a solution takes preimages along the thickening. -/
theorem opensEquiv_inverse : Q.opensEquiv.inverse = Opens.map Q.baseIso.hom := rfl

end DeformationSolution

/-- Taking preimages of opens along a continuous map preserves open covers. -/
theorem coverPreserving_opensMap {A B : TopCat.{u}} (g : A ⟶ B) :
    CoverPreserving (Opens.grothendieckTopology B) (Opens.grothendieckTopology A)
      (Opens.map g) := by
  constructor
  intro U Sv hS x hx
  obtain ⟨V, k, hk, hxV⟩ := hS (g x) hx
  exact ⟨(Opens.map g).obj V, (Opens.map g).map k, ⟨V, k, 𝟙 _, hk, by simp⟩, hxV⟩

namespace DeformationSolution

variable (Q : DeformationSolution t ht f G c)

/-- The site equivalence of a solution is cocontinuous: the inverse image of an open cover
along the inverse homeomorphism is an open cover. -/
theorem isCocontinuous_opensEquiv :
    Q.opensEquiv.functor.IsCocontinuous (Opens.grothendieckTopology X.carrier)
      (Opens.grothendieckTopology Q.X'.carrier) :=
  (Q.opensEquiv.toAdjunction.isCocontinuous_iff_coverPreserving _ _).mpr
    (coverPreserving_opensMap Q.baseIso.hom)

/-- The thickened structure sheaf `𝒪_{X'}`, read as a presheaf of commutative rings on the
opens of `X` through the homeomorphism underlying the thickening: its sections over `V` are the
sections of `𝒪_{X'}` over the corresponding open of `X'`. -/
noncomputable abbrev thickenedPresheaf : (Opens X.carrier)ᵒᵖ ⥤ CommRingCat.{u} :=
  (Opens.map Q.baseIso.inv).op ⋙ Q.X'.presheaf

/-- Pushing `𝒪_X` forward along the homeomorphism and back returns `𝒪_X`. -/
noncomputable def pushforwardRoundTrip :
    ((Opens.map Q.baseIso.inv).op ⋙
        (TopCat.Presheaf.pushforward CommRingCat Q.i.hom.base).obj X.presheaf :
      (Opens X.carrier)ᵒᵖ ⥤ CommRingCat.{u}) ≅ X.presheaf :=
  (TopCat.Presheaf.Pushforward.comp Q.baseIso.hom Q.baseIso.inv X.presheaf).symm ≪≫
    TopCat.Presheaf.pushforwardEq Q.baseIso.hom_inv_id X.presheaf ≪≫
      TopCat.Presheaf.Pushforward.id X.presheaf

/-- The reduction `𝒪_{X'} ⟶ 𝒪_X` of the thickening of a solution, read on the opens of `X`. -/
noncomputable def thickenedReduction : Q.thickenedPresheaf ⟶ X.presheaf :=
  Functor.whiskerLeft (Opens.map Q.baseIso.inv).op Q.i.hom.c ≫ Q.pushforwardRoundTrip.hom

/-- The reduction, read on the opens of `X`, is still locally surjective: local surjectivity is
inherited by restriction along the cocontinuous site equivalence, and composing with an
isomorphism of presheaves does not affect it. -/
theorem isLocallySurjective_thickenedReduction :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
      Q.thickenedReduction := by
  have := Q.isCocontinuous_opensEquiv
  have h0 : Presheaf.IsLocallySurjective (Opens.grothendieckTopology Q.X'.carrier)
      Q.i.hom.c := isLocallySurjective_comorphism_of_isThickening Q.i Q.i_firstOrder.1
  have h1 : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
      (Functor.whiskerLeft (Opens.map Q.baseIso.inv).op Q.i.hom.c) :=
    Presheaf.isLocallySurjective_whisker (Opens.grothendieckTopology X.carrier)
      (Opens.grothendieckTopology Q.X'.carrier) Q.opensEquiv.functor Q.i.hom.c
  rw [DeformationSolution.thickenedReduction]
  infer_instance

/-- Taking the open of `X'` matching an open of `X`, and then the open of `X` matching that,
returns the original open. -/
theorem opens_roundTrip (V : Opens X.carrier) :
    (Opens.map Q.baseIso.hom).obj ((Opens.map Q.baseIso.inv).obj V) = V := by
  rw [← Opens.map_comp_obj, Q.baseIso.hom_inv_id, Opens.map_id_obj]

/-- The round trip in the other direction. -/
theorem opens_roundTrip' (V : Opens Q.X'.carrier) :
    (Opens.map Q.baseIso.inv).obj ((Opens.map Q.baseIso.hom).obj V) = V := by
  rw [← Opens.map_comp_obj, Q.baseIso.inv_hom_id, Opens.map_id_obj]

/-- The restriction map of `𝒪_X` identifying the sections over the round trip of an open with
the sections over that open. -/
noncomputable abbrev roundTripHom (U : (Opens X.carrier)ᵒᵖ) :
    (Opens.map Q.baseIso.hom).op.obj ((Opens.map Q.baseIso.inv).op.obj U) ⟶ U :=
  eqToHom (congrArg op (Q.opens_roundTrip U.unop))

/-- The round trip identification is, on sections, the restriction along the round trip of the
open; the opens form a poset, so there is only one such restriction map. -/
theorem pushforwardRoundTrip_hom_app (U : (Opens X.carrier)ᵒᵖ) :
    Q.pushforwardRoundTrip.hom.app U = X.presheaf.map (Q.roundTripHom U) := by
  simp only [pushforwardRoundTrip]
  exact congrArg X.presheaf.map (Subsingleton.elim _ _)

/-- The reduction, read on the opens of `X`, is the comorphism of the thickening followed by
the round-trip identification of opens. -/
theorem thickenedReduction_app (U : (Opens X.carrier)ᵒᵖ)
    (x : Q.thickenedPresheaf.obj U) :
    (Q.thickenedReduction.app U).hom x =
      (X.presheaf.map (Q.roundTripHom U)).hom
        ((Q.i.hom.c.app ((Opens.map Q.baseIso.inv).op.obj U)).hom x) := by
  simp only [thickenedReduction, NatTrans.comp_app, Functor.whiskerLeft_app,
    Q.pushforwardRoundTrip_hom_app]
  rfl

/-- A section of the prescribed module over the open of `X'` matching an open `U` of `X`, read
as a section over `U` itself. -/
noncomputable def descendSection {U : (Opens X.carrier)ᵒᵖ}
    (g : ((modulePushforward Q.i).obj G).val.obj ((Opens.map Q.baseIso.inv).op.obj U)) :
    G.val.obj U :=
  G.val.map (Q.roundTripHom U) g

/-- Reading the zero section over the matching open gives the zero section. -/
@[simp]
theorem descendSection_zero {U : (Opens X.carrier)ᵒᵖ} :
    Q.descendSection (0 : ((modulePushforward Q.i).obj G).val.obj
      ((Opens.map Q.baseIso.inv).op.obj U)) = 0 :=
  map_zero (G.val.map (Q.roundTripHom U)).hom

/-- Reading a section over the matching open is additive. -/
theorem descendSection_add {U : (Opens X.carrier)ᵒᵖ}
    (g h : ((modulePushforward Q.i).obj G).val.obj ((Opens.map Q.baseIso.inv).op.obj U)) :
    Q.descendSection (g + h) = Q.descendSection g + Q.descendSection h :=
  map_add (G.val.map (Q.roundTripHom U)).hom g h

/-- Reading a section over the matching open is semilinear over the reduction. -/
theorem descendSection_smul {U : (Opens X.carrier)ᵒᵖ}
    (x : Q.thickenedPresheaf.obj U)
    (g : ((modulePushforward Q.i).obj G).val.obj ((Opens.map Q.baseIso.inv).op.obj U)) :
    Q.descendSection (x • g) =
      (Q.thickenedReduction.app U).hom x • Q.descendSection g := by
  rw [Q.thickenedReduction_app U x]
  exact G.val.map_smul (Q.roundTripHom U) _ g

/-- Two chains of restriction maps of `𝒪_X`-modules between the same opens agree: the opens
form a poset, so the two composites are the same morphism of the site. -/
private theorem map_comp_apply_eq {A B B' C' : (Opens X.carrier)ᵒᵖ}
    (k₁ : A ⟶ B) (k₂ : B ⟶ C') (j₁ : A ⟶ B') (j₂ : B' ⟶ C') (x : G.val.obj A) :
    G.val.map k₂ (G.val.map k₁ x) = G.val.map j₂ (G.val.map j₁ x) := by
  rw [← PresheafOfModules.map_comp_apply, ← PresheafOfModules.map_comp_apply]
  exact G.val.congr_map_apply (Subsingleton.elim _ _) x

/-- Reading a section over the matching open commutes with the restriction maps of the site. -/
theorem descendSection_naturality {U V : (Opens X.carrier)ᵒᵖ} (k : U ⟶ V)
    (g : ((modulePushforward Q.i).obj G).val.obj ((Opens.map Q.baseIso.inv).op.obj U)) :
    Q.descendSection (((modulePushforward Q.i).obj G).val.map
        ((Opens.map Q.baseIso.inv).op.map k) g) = G.val.map k (Q.descendSection g) :=
  map_comp_apply_eq ((Opens.map Q.baseIso.hom).op.map ((Opens.map Q.baseIso.inv).op.map k))
    (Q.roundTripHom V) (Q.roundTripHom U) k g

/-- The reduction read on the opens of `X` is injective exactly where the reduction of the
thickening is: the two differ by the restriction along an isomorphism of opens. -/
theorem comorphism_eq_zero_of_thickenedReduction_eq_zero {U : (Opens X.carrier)ᵒᵖ}
    (x : Q.thickenedPresheaf.obj U) (hx : (Q.thickenedReduction.app U).hom x = 0) :
    (Q.i.hom.c.app ((Opens.map Q.baseIso.inv).op.obj U)).hom x = 0 := by
  have hiso : IsIso (X.presheaf.map (Q.roundTripHom U)) := by
    rw [roundTripHom]; infer_instance
  have hinj : Function.Injective (X.presheaf.map (Q.roundTripHom U)).hom :=
    (ConcreteCategory.bijective_of_isIso (X.presheaf.map (Q.roundTripHom U))).1
  exact hinj (((Q.thickenedReduction_app U x).symm.trans hx).trans
    (map_zero (X.presheaf.map (Q.roundTripHom U)).hom).symm)

end DeformationSolution

namespace SolutionHom

variable {Q : DeformationSolution t ht f G c} (e : SolutionHom Q Q)

/-- The derivation of `𝒪_{X'}` attached to an endomorphism of a solution, read on the opens of
`X`: on a section it is the difference between the image of that section and the section
itself, which lies in the prescribed module. -/
noncomputable def descendDiff {U : (Opens X.carrier)ᵒᵖ} :
    Q.thickenedPresheaf.obj U →+ G.val.obj U :=
  AddMonoidHom.mk'
    (fun x => Q.descendSection (e.diff ((Opens.map Q.baseIso.inv).op.obj U) x))
    (fun x y => by rw [e.diff_add, Q.descendSection_add])

/-- The value of the difference derivation, read on the opens of `X`. -/
theorem descendDiff_apply {U : (Opens X.carrier)ᵒᵖ} (x : Q.thickenedPresheaf.obj U) :
    e.descendDiff x = Q.descendSection (e.diff ((Opens.map Q.baseIso.inv).op.obj U) x) := rfl

/-- The Leibniz rule for the difference derivation read on the opens of `X`, the scalars acting
through the reduction. -/
theorem descendDiff_mul {U : (Opens X.carrier)ᵒᵖ} (x y : Q.thickenedPresheaf.obj U) :
    e.descendDiff (x * y) =
      (Q.thickenedReduction.app U).hom x • e.descendDiff y +
        (Q.thickenedReduction.app U).hom y • e.descendDiff x := by
  rw [descendDiff_apply, descendDiff_apply, descendDiff_apply, e.diff_mul,
    Q.descendSection_add, Q.descendSection_smul, Q.descendSection_smul]

/-- The difference derivation read on the opens of `X` commutes with restriction. -/
theorem descendDiff_map {U V : (Opens X.carrier)ᵒᵖ} (k : U ⟶ V)
    (x : Q.thickenedPresheaf.obj U) :
    e.descendDiff ((Q.thickenedPresheaf.map k).hom x) = G.val.map k (e.descendDiff x) := by
  rw [descendDiff_apply, descendDiff_apply, ← Q.descendSection_naturality k]
  exact congrArg Q.descendSection
    (e.diff_naturality ((Opens.map Q.baseIso.inv).op.map k) x)

/-- The difference derivation read on the opens of `X` kills the kernel of the reduction, so it
factors through the sectionwise quotient by that kernel. -/
theorem descendDiff_eq_zero_of_thickenedReduction_eq_zero {U : (Opens X.carrier)ᵒᵖ}
    (x : Q.thickenedPresheaf.obj U) (hx : (Q.thickenedReduction.app U).hom x = 0) :
    e.descendDiff x = 0 := by
  obtain ⟨g, hg⟩ := Q.exists_incl x
    (Q.comorphism_eq_zero_of_thickenedReduction_eq_zero x hx)
  rw [descendDiff_apply, ← hg, e.diff_incl, DeformationSolution.descendSection_zero]

/-- The difference derivation, lifted to the sectionwise quotient of `𝒪_{X'}` by the kernel of
the reduction. On that quotient the reduction becomes locally bijective, which is what lets the
derivation descend to `𝒪_X`. -/
noncomputable def descendDiffQuot {U : (Opens X.carrier)ᵒᵖ} :
    (Stacks.Sites.Conormal.quotientPresheaf Q.thickenedReduction).obj U →+ G.val.obj U :=
  QuotientAddGroup.lift
    (Stacks.Sites.Conormal.kernelIdeal Q.thickenedReduction U).toAddSubgroup e.descendDiff
    (fun x hx => e.descendDiff_eq_zero_of_thickenedReduction_eq_zero x
      (RingHom.mem_ker.1 ((Submodule.mem_toAddSubgroup _).1 hx)))

/-- The lifted difference derivation computes the difference derivation on representatives. -/
theorem descendDiffQuot_mk {U : (Opens X.carrier)ᵒᵖ} (x : Q.thickenedPresheaf.obj U) :
    e.descendDiffQuot ((Stacks.Sites.Conormal.toQuotient Q.thickenedReduction).app U x) =
      e.descendDiff x := rfl

/-- The injection of the sectionwise quotient into `𝒪_X` is the reduction on representatives. -/
theorem quotientToTarget_mk {U : (Opens X.carrier)ᵒᵖ} (x : Q.thickenedPresheaf.obj U) :
    ((Stacks.Sites.Conormal.quotientToTarget Q.thickenedReduction).app U).hom
        ((Stacks.Sites.Conormal.toQuotient Q.thickenedReduction).app U x) =
      (Q.thickenedReduction.app U).hom x := rfl

/-- The Leibniz rule for the lifted difference derivation, the scalars acting through the
injection of the quotient into `𝒪_X`. -/
theorem descendDiffQuot_mul {U : (Opens X.carrier)ᵒᵖ}
    (a b : (Stacks.Sites.Conormal.quotientPresheaf Q.thickenedReduction).obj U) :
    e.descendDiffQuot (a * b) =
      ((Stacks.Sites.Conormal.quotientToTarget Q.thickenedReduction).app U).hom a •
          e.descendDiffQuot b +
        ((Stacks.Sites.Conormal.quotientToTarget Q.thickenedReduction).app U).hom b •
          e.descendDiffQuot a := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  exact e.descendDiff_mul a b

/-- The lifted difference derivation commutes with restriction. -/
theorem descendDiffQuot_map {U V : (Opens X.carrier)ᵒᵖ} (k : U ⟶ V)
    (a : (Stacks.Sites.Conormal.quotientPresheaf Q.thickenedReduction).obj U) :
    e.descendDiffQuot
        (((Stacks.Sites.Conormal.quotientPresheaf Q.thickenedReduction).map k).hom a) =
      G.val.map k (e.descendDiffQuot a) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact e.descendDiff_map k a

/-- The lifted difference derivation kills the unit section. -/
theorem descendDiffQuot_one {U : (Opens X.carrier)ᵒᵖ} :
    e.descendDiffQuot
        (1 : (Stacks.Sites.Conormal.quotientPresheaf Q.thickenedReduction).obj U) = 0 := by
  show e.descendDiff (1 : Q.thickenedPresheaf.obj U) = 0
  rw [descendDiff_apply, e.diff_one, DeformationSolution.descendSection_zero]

open Stacks.Sites.Conormal AlgebraicGeometry.SheafOfModules in
/-- **The descent.** The difference derivation of an endomorphism of a solution, a derivation
of the thickened structure sheaf `𝒪_{X'}` vanishing on the ideal, descends to a derivation of
`𝒪_X`, and in exactly one way. The reduction `𝒪_{X'} ⟶ 𝒪_X` is only locally surjective, so this
is not a sectionwise construction: it is the extension of a derivation along the locally
bijective map `𝒪_{X'}/ker ⟶ 𝒪_X`. -/
theorem existsUnique_intermediateDerivation :
    ∃! D : PresheafOfModulesOfCommRing.Derivation' G.val (constIntMap X.presheaf),
      ∀ (U : (Opens X.carrier)ᵒᵖ)
        (a : (quotientPresheaf Q.thickenedReduction).obj U),
        D.d (((quotientToTarget Q.thickenedReduction).app U).hom a) =
          e.descendDiffQuot a := by
  have := Q.isLocallySurjective_thickenedReduction
  exact existsUnique_derivation_extension.{u} (Opens.grothendieckTopology X.carrier)
    (quotientToTarget Q.thickenedReduction)
    (constIntMap (quotientPresheaf Q.thickenedReduction))
    (constIntMap X.presheaf)
    (𝟙 (constIntPresheaf X.carrier))
    (fun U s => map_intCast _ _)
    G.isSheaf
    (fun {U} => e.descendDiffQuot)
    (fun x y => e.descendDiffQuot_mul x y)
    (fun k x => e.descendDiffQuot_map k x)
    (fun s => constIntMap_app_eq_zero _ e.descendDiffQuot_one s)

open Stacks.Sites.Conormal AlgebraicGeometry.SheafOfModules in
/-- The descended derivation of `𝒪_X`, before its base is recognised as `f⁻¹𝒪_S`. -/
noncomputable def toDerivationAux :
    PresheafOfModulesOfCommRing.Derivation' G.val (constIntMap X.presheaf) :=
  e.existsUnique_intermediateDerivation.choose

open Stacks.Sites.Conormal in
/-- The characteristic property of the descended derivation, read on the opens of `X`. -/
theorem toDerivationAux_thickenedReduction (U : (Opens X.carrier)ᵒᵖ)
    (x : Q.thickenedPresheaf.obj U) :
    e.toDerivationAux.d ((Q.thickenedReduction.app U).hom x) = e.descendDiff x :=
  e.existsUnique_intermediateDerivation.choose_spec.1 U
    ((toQuotient Q.thickenedReduction).app U x)

/-- Two chains of restriction maps of a structure sheaf between the same opens agree. -/
private theorem presheaf_map_comp_eq {T : RingedSpace.{u, u}} {A B C' : (Opens T.carrier)ᵒᵖ}
    (k₁ : A ⟶ B) (k₂ : B ⟶ C') (k₃ : A ⟶ C') (y : T.presheaf.obj A) :
    (T.presheaf.map k₂).hom ((T.presheaf.map k₁).hom y) = (T.presheaf.map k₃).hom y := by
  have h1 : T.presheaf.map k₁ ≫ T.presheaf.map k₂ = T.presheaf.map k₃ := by
    rw [← Functor.map_comp]
    exact congrArg T.presheaf.map (Subsingleton.elim _ _)
  exact congrArg (fun k => (ConcreteCategory.hom k) y) h1

/-- Restriction along an isomorphism of opens is injective on sections of an `𝒪_X`-module. -/
private theorem map_inj {A B : (Opens X.carrier)ᵒᵖ} (k : A ⟶ B) [IsIso k]
    {y z : G.val.obj A} (h : G.val.map k y = G.val.map k z) : y = z := by
  have h1 : G.val.map (inv k) (G.val.map k y) = G.val.map (inv k) (G.val.map k z) :=
    congrArg (fun w => G.val.map (inv k) w) h
  rw [← PresheafOfModules.map_comp_apply, ← PresheafOfModules.map_comp_apply,
    IsIso.hom_inv_id] at h1
  simp only [PresheafOfModules.map_id] at h1
  exact h1

/-- **The characteristic property of the descended derivation**, read on the opens of `X'`: on
the reduction of a section of `𝒪_{X'}` it is the difference by which the endomorphism moves
that section. -/
theorem toDerivationAux_comorphism (W : (Opens Q.X'.carrier)ᵒᵖ)
    (x : Q.X'.presheaf.obj W) :
    e.toDerivationAux.d ((Q.i.hom.c.app W).hom x) = e.diff W x := by
  have hWW : (Opens.map Q.baseIso.inv).op.obj ((Opens.map Q.baseIso.hom).op.obj W) = W :=
    congrArg op (Q.opens_roundTrip' W.unop)
  set U : (Opens X.carrier)ᵒᵖ := (Opens.map Q.baseIso.hom).op.obj W with hU
  set h : W ⟶ (Opens.map Q.baseIso.inv).op.obj U := eqToHom hWW.symm with hh
  set y : Q.X'.presheaf.obj ((Opens.map Q.baseIso.inv).op.obj U) :=
    (Q.X'.presheaf.map h).hom x with hy
  have hisoR : IsIso (Q.roundTripHom U) := by
    rw [DeformationSolution.roundTripHom]
    infer_instance
  have hisoH : IsIso ((Opens.map Q.baseIso.hom).op.map h) := by
    rw [hh]
    infer_instance
  have hred := e.toDerivationAux_thickenedReduction U y
  rw [Q.thickenedReduction_app] at hred
  have hd := e.toDerivationAux.d_map (Q.roundTripHom U)
    ((Q.i.hom.c.app ((Opens.map Q.baseIso.inv).op.obj U)).hom y)
  have h1 := map_inj (Q.roundTripHom U) (hd.symm.trans hred)
  have hnat := congrArg (fun k => (ConcreteCategory.hom k) x) (Q.i.hom.c.naturality h)
  refine map_inj ((Opens.map Q.baseIso.hom).op.map h) ?_
  refine Eq.trans (e.toDerivationAux.d_map ((Opens.map Q.baseIso.hom).op.map h)
    ((Q.i.hom.c.app W).hom x)).symm ?_
  exact (congrArg e.toDerivationAux.d hnat.symm).trans (h1.trans (e.diff_naturality h x))

/-- The descended derivation kills every section pulled back from the thickened base along the
deformed structure morphism: an endomorphism of a solution is a morphism over `S'`. -/
theorem toDerivationAux_deformedStructureMap (W : (Opens S'.carrier)ᵒᵖ)
    (b : S'.presheaf.obj W) :
    e.toDerivationAux.d (((Q.i ≫ Q.f').hom.c.app W).hom b) = 0 := by
  show e.toDerivationAux.d ((Q.i.hom.c.app ((Opens.map Q.f'.hom.base).op.obj W)).hom
      ((Q.f'.hom.c.app W).hom b)) = 0
  rw [e.toDerivationAux_comorphism, e.diff_baseMap]
  rfl

/-- The same, read through the commuting square of the solution: the derivation kills every
section pulled back along `f ≫ t`. -/
theorem toDerivationAux_compStructureMap (W : (Opens S'.carrier)ᵒᵖ)
    (b : S'.presheaf.obj W) :
    e.toDerivationAux.d (((f ≫ t).hom.c.app W).hom b) = 0 := by
  rw [← Q.comm]
  exact e.toDerivationAux_deformedStructureMap W b

/-- **The descended derivation is a derivation over `f⁻¹𝒪_S`.** A section of `𝒪_S` lifts, near
every point, to a section of `𝒪_{S'}` because `t` is a thickening, and on such a lift the
derivation already vanishes; the values glue because the prescribed module is a sheaf. -/
theorem toDerivationAux_structureMap (V : Opens S.carrier) (b : S.presheaf.obj (op V)) :
    e.toDerivationAux.d ((f.hom.c.app (op V)).hom b) = 0 := by
  have htiso : IsIso t.hom.base := ht.1.1
  set tb : S.carrier ≅ S'.carrier := asIso t.hom.base with htb
  have hV : (Opens.map tb.hom).obj ((Opens.map tb.inv).obj V) = V := by
    rw [← Opens.map_comp_obj, tb.hom_inv_id, Opens.map_id_obj]
  set V' : Opens S'.carrier := (Opens.map tb.inv).obj V with hV'
  set b₀ : S.presheaf.obj (op ((Opens.map t.hom.base).obj V')) :=
    (S.presheaf.map (eqToHom (congrArg op hV.symm))).hom b with hb₀
  have htc : TopCat.Presheaf.IsLocallySurjective t.hom.c :=
    isLocallySurjective_comorphism_of_isThickening t ht.1
  have hsurj := (TopCat.Presheaf.isLocallySurjective_iff t.hom.c).1 htc V' b₀
  refine TopCat.Presheaf.IsSheaf.section_ext G.isSheaf ?_
  intro x hx
  have hinv : ∀ w : S.carrier, tb.inv (tb.hom w) = w :=
    fun w => ConcreteCategory.congr_hom tb.hom_inv_id w
  have hyV' : t.hom.base (f.hom.base x) ∈ V' := by
    show tb.inv (tb.hom (f.hom.base x)) ∈ V
    rw [hinv]
    exact hx
  obtain ⟨V'', hV''V', ⟨a, ha⟩, hyV''⟩ := hsurj (t.hom.base (f.hom.base x)) hyV'
  have hV₁ : (Opens.map t.hom.base).obj V'' ≤ V := by
    intro z hz
    have h1 : z ∈ (Opens.map tb.hom).obj V'' := hz
    have h2 : tb.hom z ∈ V' := hV''V' h1
    show z ∈ V
    rw [← hinv z]
    exact h2
  refine ⟨(Opens.map f.hom.base).obj ((Opens.map t.hom.base).obj V''),
    fun z hz => hV₁ hz, hyV'', ?_⟩
  set j : (op V : (Opens S.carrier)ᵒᵖ) ⟶ op ((Opens.map t.hom.base).obj V'') :=
    (homOfLE hV₁).op with hj
  have hbj : (S.presheaf.map j).hom b = (t.hom.c.app (op V'')).hom a :=
    (presheaf_map_comp_eq (eqToHom (congrArg op hV.symm))
      ((Opens.map t.hom.base).op.map (homOfLE hV''V').op) j b).symm.trans ha.symm
  have hnat := congrArg (fun k => (ConcreteCategory.hom k) b) (f.hom.c.naturality j)
  refine Eq.trans ?_ (map_zero _).symm
  refine Eq.trans (e.toDerivationAux.d_map ((Opens.map f.hom.base).op.map j)
      ((f.hom.c.app (op V)).hom b)).symm ?_
  refine Eq.trans (congrArg e.toDerivationAux.d hnat.symm) ?_
  refine Eq.trans (congrArg (fun z => e.toDerivationAux.d
    ((f.hom.c.app (op ((Opens.map t.hom.base).obj V''))).hom z)) hbj) ?_
  exact e.toDerivationAux_compStructureMap (op V'') a

/-- **The derivation of `𝒪_X` over `f⁻¹𝒪_S` attached to an endomorphism of a solution.** -/
noncomputable def toDerivation :
    Stacks.Sheaves.RingedSpaceDifferentials.SDerivation f G where
  d := e.toDerivationAux.d
  d_mul := e.toDerivationAux.d_mul
  d_map := e.toDerivationAux.d_map
  d_app {U} a :=
    Stacks.Sheaves.RingedSpaceDifferentials.derivation_d_inverseImageStructureMap_eq_zero
      f G.isSheaf e.toDerivationAux e.toDerivationAux_structureMap U a

/-- The derivation attached to an endomorphism of a solution computes, on the reduction of a
section of `𝒪_{X'}`, the difference by which that endomorphism moves the section. -/
theorem toDerivation_comorphism (W : (Opens Q.X'.carrier)ᵒᵖ)
    (x : Q.X'.presheaf.obj W) :
    e.toDerivation.d ((Q.i.hom.c.app W).hom x) = e.diff W x :=
  e.toDerivationAux_comorphism W x

end SolutionHom

/-! ### The endomorphism attached to a derivation -/

/-- A relative derivation of `𝒪_X` over `f⁻¹𝒪_S` annihilates every section pulled back along
`f^♯`: such a section lies in the image of `f⁻¹𝒪_S ⟶ 𝒪_X`, which the derivation kills by
definition. The same statement for the universal derivation is
`universalDerivation_d_structureSheafMap`. -/
theorem derivation_d_structureSheafMap
    (D : Stacks.Sheaves.RingedSpaceDifferentials.SDerivation f G)
    (V : (Opens S.carrier)ᵒᵖ) (b : S.presheaf.obj V) :
    D.d ((f.hom.c.app V).hom b) = 0 := by
  have e : Stacks.Sheaves.RingedSpaceDifferentials.structureSheafMap f =
      (Stacks.Sheaves.RingedSpaceDifferentials.sheafAdjunction f).unit.app S.sheaf ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).map
          (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap f) := by
    rw [← Stacks.Sheaves.RingedSpaceDifferentials.homEquiv_inverseImageStructureMap f,
      Adjunction.homEquiv_unit]
  have e2 : (f.hom.c.app V).hom b
      = ((Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap f).hom.app
            ((Opens.map f.hom.base).op.obj V)).hom
          (((Stacks.Sheaves.RingedSpaceDifferentials.sheafAdjunction f).unit.app
            S.sheaf).hom.app V b) :=
    congrArg (fun z : S.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).obj X.sheaf =>
        (z.hom.app V).hom b) e
  exact (congrArg D.d e2).trans (PresheafOfModulesOfCommRing.Derivation'.d_app D _)

namespace DeformationSolution

variable (Q : DeformationSolution t ht f G c)

open Stacks.Sheaves.RingedSpaceDifferentials in
/-- The value of a relative derivation of `𝒪_X` on the reduction of a section of `𝒪_{X'}`,
read as a section of the prescribed module over the corresponding open of `X'`. -/
noncomputable def dval (D : SDerivation f G) {W : (Opens Q.X'.carrier)ᵒᵖ}
    (x : Q.X'.presheaf.obj W) : ((modulePushforward Q.i).obj G).val.obj W :=
  D.d ((Q.i.hom.c.app W).hom x)

section Dval

open Stacks.Sheaves.RingedSpaceDifferentials

variable (D : Stacks.Sheaves.RingedSpaceDifferentials.SDerivation f G)

include D in
/-- A derivation kills the unit section. -/
theorem dval_one {W : (Opens Q.X'.carrier)ᵒᵖ} :
    Q.dval D (1 : Q.X'.presheaf.obj W) = 0 :=
  (congrArg D.d (map_one (Q.i.hom.c.app W).hom)).trans (D.d_one _)

/-- A derivation kills the zero section. -/
theorem dval_zero {W : (Opens Q.X'.carrier)ᵒᵖ} :
    Q.dval D (0 : Q.X'.presheaf.obj W) = 0 :=
  (congrArg D.d (map_zero (Q.i.hom.c.app W).hom)).trans (map_zero D.d)

/-- A derivation is additive on the reductions of sections of `𝒪_{X'}`. -/
theorem dval_add {W : (Opens Q.X'.carrier)ᵒᵖ} (x y : Q.X'.presheaf.obj W) :
    Q.dval D (x + y) = Q.dval D x + Q.dval D y :=
  (congrArg D.d (map_add (Q.i.hom.c.app W).hom x y)).trans (map_add D.d _ _)

/-- The Leibniz rule on the reductions of sections of `𝒪_{X'}`, the scalars acting through the
reduction. -/
theorem dval_mul {W : (Opens Q.X'.carrier)ᵒᵖ} (x y : Q.X'.presheaf.obj W) :
    Q.dval D (x * y) = x • Q.dval D y + y • Q.dval D x :=
  (congrArg D.d (map_mul (Q.i.hom.c.app W).hom x y)).trans (D.d_mul _ _)

/-- The values of a derivation on the reductions of sections of `𝒪_{X'}` commute with
restriction. -/
theorem dval_naturality {W W' : (Opens Q.X'.carrier)ᵒᵖ} (k : W ⟶ W')
    (x : Q.X'.presheaf.obj W) :
    Q.dval D ((Q.X'.presheaf.map k).hom x) =
      ((modulePushforward Q.i).obj G).val.map k (Q.dval D x) :=
  (congrArg D.d (congrArg (fun z => (ConcreteCategory.hom z) x)
    (Q.i.hom.c.naturality k))).trans
      (D.d_map ((Opens.map Q.i.hom.base).op.map k) ((Q.i.hom.c.app W).hom x))

/-- The endomorphism `x ↦ x + δ(x mod 𝒢)` of the thickened structure sheaf attached to a
relative derivation `δ` of `𝒪_X`. It is a homomorphism of sheaves of rings because the ideal
has square zero and `δ` satisfies the Leibniz rule. -/
noncomputable def derivationComorphism : Q.X'.presheaf ⟶ Q.X'.presheaf where
  app W := CommRingCat.ofHom
    { toFun x := x + Q.incl (Q.dval D x)
      map_one' := by rw [Q.dval_one, Q.incl_zero, add_zero]
      map_zero' := by rw [Q.dval_zero, Q.incl_zero, add_zero]
      map_add' x y := by
        change x + y + Q.incl (Q.dval D (x + y)) = _
        rw [Q.dval_add, Q.incl_add]
        abel
      map_mul' x y := by
        have h0 : Q.incl (Q.dval D x) * Q.incl (Q.dval D y) = 0 := Q.incl_mul_incl _ _
        change x * y + Q.incl (Q.dval D (x * y)) = _
        rw [Q.dval_mul, Q.incl_add, ← Q.mul_incl, ← Q.mul_incl]
        linear_combination -h0 }
  naturality W W' k := by
    refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
    change (Q.X'.presheaf.map k).hom x + Q.incl (Q.dval D ((Q.X'.presheaf.map k).hom x)) =
      (Q.X'.presheaf.map k).hom (x + Q.incl (Q.dval D x))
    rw [map_add, ← Q.incl_naturality k (Q.dval D x), Q.dval_naturality]

end Dval

/-- The endomorphism attached to a derivation, on sections. -/
theorem derivationComorphism_app
    (D : Stacks.Sheaves.RingedSpaceDifferentials.SDerivation f G)
    (W : (Opens Q.X'.carrier)ᵒᵖ) (x : Q.X'.presheaf.obj W) :
    ((Q.derivationComorphism D).app W).hom x = x + Q.incl (Q.dval D x) := rfl

/-- The endomorphism of the deformed ringed space attached to a relative derivation of `𝒪_X`:
the identity on the underlying space, and `x ↦ x + δ(x mod 𝒢)` on the structure sheaf. -/
noncomputable def derivationHom
    (D : Stacks.Sheaves.RingedSpaceDifferentials.SDerivation f G) : Q.X' ⟶ Q.X' :=
  ⟨⟨𝟙 Q.X'.carrier, Q.derivationComorphism D⟩⟩

variable (D : Stacks.Sheaves.RingedSpaceDifferentials.SDerivation f G)

/-- A derivation of `𝒪_X` vanishes on the prescribed ideal of a solution, which the reduction
kills. -/
theorem dval_incl {W : (Opens Q.X'.carrier)ᵒᵖ}
    (u : ((modulePushforward Q.i).obj G).val.obj W) : Q.dval D (Q.incl u) = 0 := by
  show D.d ((Q.i.hom.c.app W).hom (Q.incl u)) = 0
  rw [show (Q.i.hom.c.app W).hom (Q.incl u) =
    (0 : ((modulePushforward Q.i).obj (SheafOfModules.unit (structureSheafRing X))).val.obj W)
      from Q.reduction_incl u]
  exact map_zero D.d

include D in
/-- The endomorphism attached to a derivation is a morphism under `X`. -/
theorem derivationHom_thickening_comm : Q.i ≫ Q.derivationHom D = Q.i := by
  have key : Q.derivationComorphism D ≫ Q.i.hom.c = Q.i.hom.c := by
    ext W x
    show (Q.i.hom.c.app (op W)).hom (x + Q.incl (Q.dval D x)) =
      (Q.i.hom.c.app (op W)).hom x
    rw [map_add, show (Q.i.hom.c.app (op W)).hom (Q.incl (Q.dval D x)) =
      (0 : ((TopCat.Presheaf.pushforward CommRingCat Q.i.hom.base).obj X.presheaf).obj (op W))
        from Q.reduction_incl _, add_zero]
  exact congrArg (fun k => (⟨⟨Q.i.hom.base, k⟩⟩ : X ⟶ Q.X')) key

/-- A derivation of `𝒪_X` over `f⁻¹𝒪_S` vanishes on every section pulled back from the thickened
base along the deformed structure morphism of a solution. -/
theorem dval_deformedStructureMap (W : (Opens S'.carrier)ᵒᵖ) (s : S'.presheaf.obj W) :
    Q.dval D ((Q.f'.hom.c.app W).hom s) = 0 := by
  show D.d (((Q.i ≫ Q.f').hom.c.app W).hom s) = 0
  rw [Q.comm]
  exact derivation_d_structureSheafMap D ((Opens.map t.hom.base).op.obj W)
    ((t.hom.c.app W).hom s)

include D in
/-- The endomorphism attached to a derivation is a morphism over `S'`. -/
theorem derivationHom_base_comm : Q.derivationHom D ≫ Q.f' = Q.f' := by
  have key : Q.f'.hom.c ≫
      (TopCat.Presheaf.pushforward CommRingCat Q.f'.hom.base).map
        (Q.derivationComorphism D) = Q.f'.hom.c := by
    ext W s
    show ((Q.derivationComorphism D).app ((Opens.map Q.f'.hom.base).op.obj (op W))).hom
        ((Q.f'.hom.c.app (op W)).hom s) = (Q.f'.hom.c.app (op W)).hom s
    rw [Q.derivationComorphism_app, Q.dval_deformedStructureMap D (op W) s, Q.incl_zero,
      add_zero]
  exact congrArg (fun k => (⟨⟨Q.f'.hom.base, k⟩⟩ : Q.X' ⟶ S')) key

/-- The endomorphism attached to a derivation is the identity under `X`, so pushing a module
forward along `i` is pushing it forward along `i` followed by that endomorphism. -/
private theorem modulePushforward_eq_derivationHom :
    modulePushforward Q.i = modulePushforward (Q.i ≫ Q.derivationHom D) :=
  (congrArg (fun k : X ⟶ Q.X' => modulePushforward k)
    (Q.derivationHom_thickening_comm D)).symm

/-- The comparison isomorphism between the two pushforwards is the transport carried by
`modulePushforward_eq_derivationHom`: the other factor of `pushforwardIsoOfComp` is an identity,
because pushing forward along a composite is pushing forward twice on the nose. -/
private theorem pushforwardIsoOfComp_derivationHom_hom_app :
    (pushforwardIsoOfComp Q.i (Q.derivationHom D) Q.i
        (Q.derivationHom_thickening_comm D)).hom.app G =
      (eqToIso (Q.modulePushforward_eq_derivationHom D)).hom.app G := by
  simp only [pushforwardIsoOfComp, Iso.trans_hom, NatTrans.comp_app,
    modulePushforwardCompSymm, Iso.symm_hom, modulePushforwardComp_inv_app]
  exact Category.comp_id _

/-- That transport leaves the sections of the prescribed ideal untouched. -/
private theorem eqToIso_modulePushforward_app_val_app
    (W : (Opens Q.X'.carrier)ᵒᵖ) (u : ((modulePushforward Q.i).obj G).val.obj W) :
    (((eqToIso (Q.modulePushforward_eq_derivationHom D)).hom.app G).val.app W).hom u = u :=
  eq_of_heq (SolutionHom.eqToIso_hom_app_val_app_heq _ G W u)

/-- The left-hand side of the ideal condition, read on a section: a section of the prescribed
ideal is included into the thickened structure sheaf and then moved by the comorphism of the
endomorphism attached to the derivation. Both passages are sectionwise, so this is `rfl`. -/
private theorem idealInclusion_comp_structureSheafHom_val_app
    (W : (Opens Q.X'.carrier)ᵒᵖ) (u : ((modulePushforward Q.i).obj G).val.obj W) :
    ((Q.idealInclusion ≫ SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom (Q.derivationHom D))).val.app W).hom u =
      ((Q.derivationComorphism D).app W).hom (Q.incl u) :=
  rfl

/-- The right-hand side of the ideal condition, read on a section: the transport is applied and
the result included. The endomorphism is the identity on the underlying space, so the pushforward
of the inclusion moves no open set and is the inclusion over `W` itself; this too is `rfl`. The
two sides are stated separately because asking for both reductions in one goal costs the
elaborator several times the default heartbeat budget. -/
private theorem eqToIso_comp_modulePushforward_map_val_app
    (W : (Opens Q.X'.carrier)ᵒᵖ) (u : ((modulePushforward Q.i).obj G).val.obj W) :
    (((eqToIso (Q.modulePushforward_eq_derivationHom D)).hom.app G ≫
        (modulePushforward (Q.derivationHom D)).map Q.idealInclusion).val.app W).hom u =
      (Q.idealInclusion.val.app W).hom
        ((((eqToIso (Q.modulePushforward_eq_derivationHom D)).hom.app G).val.app W).hom u) :=
  rfl

include D in
/-- The endomorphism attached to a derivation is the identity on the prescribed ideal. -/
theorem derivationHom_kernel_comm :
    Q.idealInclusion ≫ SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom (Q.derivationHom D)) =
      (pushforwardIsoOfComp Q.i (Q.derivationHom D) Q.i
          (Q.derivationHom_thickening_comm D)).hom.app G ≫
        (modulePushforward (Q.derivationHom D)).map Q.idealInclusion := by
  rw [Q.pushforwardIsoOfComp_derivationHom_hom_app D]
  ext W u
  refine (Q.idealInclusion_comp_structureSheafHom_val_app D W u).trans
    (Eq.trans ?_ (Q.eqToIso_comp_modulePushforward_map_val_app D W u).symm)
  refine Eq.trans ?_ (congrArg
    (fun z : ((modulePushforward Q.i).obj G).val.obj W => (Q.idealInclusion.val.app W).hom z)
    (Q.eqToIso_modulePushforward_app_val_app D W u)).symm
  rw [Q.derivationComorphism_app D W (Q.incl u), Q.dval_incl D u, Q.incl_zero, add_zero]
  rfl

/-- **The endomorphism of a solution attached to a relative derivation of `𝒪_X`.** -/
noncomputable def derivationSolutionHom : SolutionHom Q Q where
  hom := Q.derivationHom D
  thickening_comm := Q.derivationHom_thickening_comm D
  base_comm := Q.derivationHom_base_comm D
  kernel_comm := Q.derivationHom_kernel_comm D

/-- The comorphism of the endomorphism attached to a derivation is the one it was built from. -/
theorem selfComorphism_derivationSolutionHom :
    (Q.derivationSolutionHom D).selfComorphism = Q.derivationComorphism D :=
  Category.comp_id _

/-- The endomorphism attached to a derivation moves a section by the value of that derivation. -/
theorem diff_derivationSolutionHom (W : (Opens Q.X'.carrier)ᵒᵖ)
    (x : Q.X'.presheaf.obj W) :
    (Q.derivationSolutionHom D).diff W x = Q.dval D x := by
  refine Q.incl_injective ?_
  rw [SolutionHom.incl_diff, Q.selfComorphism_derivationSolutionHom D,
    Q.derivationComorphism_app D W x]
  abel

end DeformationSolution

/-! ### Stacks 08UZ, clause (3) -/

namespace SolutionHom

/-- A morphism of solutions is determined by the underlying morphism of ringed spaces. -/
theorem ext' {Q₁ Q₂ : DeformationSolution t ht f G c} {p q : SolutionHom Q₁ Q₂}
    (h : p.hom = q.hom) : p = q := by
  cases p; cases q; cases h; rfl

end SolutionHom

namespace DeformationSolution

variable (Q : DeformationSolution t ht f G c)

/-- Reading off the derivation of the endomorphism attached to a derivation returns that
derivation: the two passages are mutually inverse in one direction. -/
theorem toDerivation_derivationSolutionHom
    (D : Stacks.Sheaves.RingedSpaceDifferentials.SDerivation f G) :
    (Q.derivationSolutionHom D).toDerivation = D := by
  have := Q.isLocallySurjective_thickenedReduction
  refine AlgebraicGeometry.SheafOfModules.derivation_ext_of_isLocallySurjective
    (Opens.grothendieckTopology X.carrier) Q.thickenedReduction G.isSheaf _ _ ?_
  intro U y
  rw [Q.thickenedReduction_app U y]
  refine Eq.trans ((Q.derivationSolutionHom D).toDerivationAux.d_map _ _) ?_
  refine Eq.trans ?_ (D.d_map (Q.roundTripHom U)
    ((Q.i.hom.c.app ((Opens.map Q.baseIso.inv).op.obj U)).hom y)).symm
  exact congrArg (fun z => G.val.map (Q.roundTripHom U) z)
    (((Q.derivationSolutionHom D).toDerivation_comorphism _ y).trans
      (Q.diff_derivationSolutionHom D _ y))

/-- Attaching an endomorphism to the derivation of an endomorphism returns that endomorphism:
the two passages are mutually inverse in the other direction. -/
theorem derivationSolutionHom_toDerivation (e : SolutionHom Q Q) :
    Q.derivationSolutionHom e.toDerivation = e := by
  refine SolutionHom.ext' ?_
  have hc : Q.derivationComorphism e.toDerivation = e.selfComorphism := by
    ext W x
    rw [Q.derivationComorphism_app]
    show x + Q.incl (e.toDerivation.d ((Q.i.hom.c.app (op W)).hom x)) =
      (e.selfComorphism.app (op W)).hom x
    rw [e.toDerivation_comorphism (op W) x, SolutionHom.incl_diff]
    abel
  show (⟨⟨𝟙 Q.X'.carrier, Q.derivationComorphism e.toDerivation⟩⟩ : Q.X' ⟶ Q.X') = e.hom
  rw [hc]
  exact e.hom_eq_mk.symm

/-- The identity automorphism of a solution moves no section. -/
theorem diff_id (W : (Opens Q.X'.carrier)ᵒᵖ) (x : Q.X'.presheaf.obj W) :
    (SolutionHom.id Q).diff W x = 0 :=
  (SolutionHom.id Q).diff_eq_zero_of_apply_eq rfl

/-- **Stacks 08UZ, clause (3)**, in terms of derivations: the endomorphisms of a solution of
the deformation problem of **Stacks 08UY** are the relative derivations of `𝒪_X` over
`f⁻¹𝒪_S` with values in `𝒢`. -/
noncomputable def solutionHomEquivSDerivation :
    SolutionHom Q Q ≃ Stacks.Sheaves.RingedSpaceDifferentials.SDerivation f G where
  toFun e := e.toDerivation
  invFun D := Q.derivationSolutionHom D
  left_inv e := Q.derivationSolutionHom_toDerivation e
  right_inv D := Q.toDerivation_derivationSolutionHom D

/-- The derivation attached to an automorphism of a solution is the difference by which that
automorphism moves the sections of the thickened structure sheaf. -/
theorem solutionHomEquivSDerivation_apply (e : SolutionHom Q Q)
    (W : (Opens Q.X'.carrier)ᵒᵖ) (x : Q.X'.presheaf.obj W) :
    Q.incl ((Q.solutionHomEquivSDerivation e).d ((Q.i.hom.c.app W).hom x)) =
      (e.selfComorphism.app W).hom x - x :=
  (congrArg Q.incl (e.toDerivation_comorphism W x)).trans (e.incl_diff W x)

section CotangentExt

attribute [local instance] HasDerivedCategory.standard

open Stacks.Sheaves.RingedSpaceCotangent in
/-- **Stacks Project, Tag 08UZ, clause (3).** Given a solution `X'` of the deformation problem
of (08UY), the automorphisms of `X'` fitting into that diagram are canonically
`Ext⁰_{𝒪_X}(L_{X/S}, 𝒢)`.

The automorphisms in question are the `SolutionHom Q Q`: morphisms of the deformed space under
`X`, over `S'`, and the identity on the prescribed ideal `𝒢`. Every one of them is invertible
by `SolutionHom.isIso_hom`, so they are the automorphisms of `X'` in the diagram, and no
invertibility hypothesis appears. Such a morphism is `x ↦ x + δ(x)` for a unique relative
derivation `δ` of `𝒪_X` over `f⁻¹𝒪_S` with values in `𝒢`
(`solutionHomEquivSDerivation`), and those derivations are
`Hom_{𝒪_X}(Ω_{X/S}, 𝒢) = Ext⁰_{𝒪_X}(L_{X/S}, 𝒢)` by corepresentability and
`extZeroCotangentAddEquiv`. The derivation attached to an automorphism is pinned down by
`solutionHomEquivSDerivation_apply`, and the automorphism attached to a derivation by
`derivationComorphism_app`. -/
noncomputable def solutionHomEquivCotangentExt :
    SolutionHom Q Q ≃ cotangentExt f G 0 :=
  (Q.solutionHomEquivSDerivation.trans
      (Stacks.Sheaves.RingedSpaceCotangent.moduleOfDifferentials_corepresentableBy
        f).homEquiv.symm).trans
    (extZeroCotangentAddEquiv f G).toEquiv.symm

end CotangentExt

end DeformationSolution

end AlgebraicGeometry.RingedSpaceThickening

end
