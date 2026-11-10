module

public import StacksFrontier.AlgebraicGeometry.DeRham.Cohomology.SupportClassPairing
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.ConormalWedgeLocal
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinTargetExcisionAbelian
public import StacksFrontier.AlgebraicGeometry.ModuleBilinearGlue.Basic
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.SupportCohomologyLinear

/-!
# The wedge pairing with the local cohomology sheaf, at the generality of Tag 0G86

Let `π : X ⟶ S` be a morphism of schemes and `i : Z ⟶ X` a closed immersion.  This file builds the
**equation-free** wedge pairing

`Ω^p_{X/S} × i_*ℋ^c_Z(Ω^c_{X/S}) ⟶ i_*ℋ^c_Z(Ω^{p+c}_{X/S})`

of [Stacks, Tag 0G88] — the multiplication of Cohomology, Remark [Stacks, Tag 0G75] in the degrees
the tag uses — with `Z` only *locally* cut out by `c` equations.  The pairing of
`StacksFrontier/AlgebraicGeometry/DeRham/Cohomology/SupportClassPairing.lean` is descended from the
extended alternating Čech complex of a **global** family of equations and so exists only when `Z`
is globally cut out; **no family of equations occurs anywhere here**, neither in the construction
nor in the proofs of the five bilinearity laws, and `c` is an arbitrary natural number — `c = 0`
included, where no local family of `c` equations cutting out `Z` exists on an open meeting the
complement of `Z`.

## The construction

A section `ω` of `Ω^p_{X/S}` over an open `V` is a **global** section of the restriction
`Ω^p_{X/S}|_V`, so multiplication by it is a morphism of sheaves of modules on `V`:
`Stacks.Gysin.localFormWedgeHom`.  The derived excision of [Stacks, Tag 0G78], in the form
`Stacks.Gysin.supportCohomologyRestrictIso`, conjugates the degree-`c` local cohomology functor of
`V` into the restriction to `V` of the one of `X`, which turns that morphism into
`Stacks.Gysin.conormalWedgeHom`, a morphism of the restrictions to `V` of the two target sheaves;
its action on the sections over `V` is the value `Stacks.Gysin.conormalWedgeVal` of the pairing.

Three of the five laws of a `Stacks.BilinearMap` are then immediate, because the value is the
action of a morphism of sheaves of modules on sections: biadditivity and homogeneity in the
*second* variable, and — crucially — compatibility with restriction *within* `V`.  The two laws
in the first variable are laws in the *morphism* rather than in the section, and they come from
the functor:

* multiplication by `ω` is additive and `𝒪`-homogeneous in `ω` because the multiplication of
  forms is a bilinear map (`Stacks.Gysin.localFormWedgeHom_add`,
  `Stacks.Gysin.localFormWedgeHom_smul`);
* the degree-`c` local cohomology functor of `V` is additive and `Γ(V, ⊤)`-linear on morphisms, by
  `Stacks.Perfect.SupportCohomologyLinear.supportCohomologySheafFunctor_additive` and
  `supportCohomologySheafFunctor_linear`, and conjugating by the derived excision preserves both
  (`Stacks.Gysin.conormalWedgeHom_add`, `Stacks.Gysin.conormalWedgeHom_smul`);
* `Stacks.AlgebraicGeometry.ModuleLimits.restrictSections` turns those into the laws on sections,
  by `Stacks.Gysin.restrictSections_add_hom` and `Stacks.Gysin.restrictSections_globalSmul`.

What is left is the compatibility of the pairing's value at `V` with its value at a smaller open
`V'`, which compares the excisions of two *different* opens.  It is proved without any coherence
of the excision, by the **unit** `Ω^{p+c}_{X/S} ⟶ (V.ι)_*(Ω^{p+c}_{X/S}|_V)` of
`AlgebraicGeometry.Scheme.Modules.restrictAdjunction`: `Stacks.Gysin.localFormWedgeExt` is
multiplication by `ω` read as a morphism of sheaves on the whole of `X` with that direct image as
its target, and `Stacks.Gysin.supportCohomology_localFormWedgeExt_app` says the pairing's
value is characterised by it.  Since both sides of the characterisation are morphisms of sheaves
on `X`, their compatibility with restriction is naturality, and the unit of `V'` factors the unit
of `V` by `Stacks.Gysin.openUnit_comp_openUnitTransport`.

## Main definitions

* `Stacks.Gysin.formWedgePair`: the multiplication `Ω^p × Ω^c ⟶ Ω^{p+c}` of the sheaf of graded
  algebras of relative differential forms, in the degrees the pairing of [Stacks, Tag 0G88]
  needs.
* `Stacks.Gysin.localFormWedgeHom`: multiplication by a section of `Ω^p_{X/S}` over `V`, as a
  morphism of the restrictions to `V`.
* `Stacks.Gysin.conormalWedgeHom`, `Stacks.Gysin.conormalWedgeVal`: the pairing over `V`.
* `Stacks.Gysin.conormalWedgePair`: **the wedge pairing of [Stacks, Tag 0G88] at the generality of
  [Stacks, Tag 0G86], at every conormal rank**, assembled from its values over the opens by
  `Stacks.AlgebraicGeometry.ModuleBilinearGlue.gluedBilinearMap` over the one-member covering
  `{⊤}`.

## Main results

* `Stacks.Gysin.conormalWedgePair_app`: over *every* open the pairing is `conormalWedgeVal`.
* `Stacks.Gysin.restrictSections_conormalWedgeHom_le`: **the pairing over an open and the pairing
  over a smaller one agree on the sections over the smaller one**, which is the clause the gluing
  needs and the only one that compares the derived excisions of two different opens.

## References

* [Stacks Project, Tag 0G88](https://stacks.math.columbia.edu/tag/0G88)
* [Stacks Project, Tag 0G86](https://stacks.math.columbia.edu/tag/0G86)
* [Stacks Project, Tag 0G78](https://stacks.math.columbia.edu/tag/0G78)
* [Stacks Project, Tag 0G75](https://stacks.math.columbia.edu/tag/0G75)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.Scheme.Hom
open Stacks.AlgebraicGeometry.ModuleLimits
open Stacks.Perfect.CechDerivedSupport (equationsClosedSet)
open Stacks.Perfect.SupportedFraction
open Stacks.Perfect.CechPairing

universe u

namespace Stacks.Gysin

variable {Z X S : Scheme.{u}}

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] isQuasicoherent_relativeDifferentialForms

/-! ### Multiplication by a section over an open -/

/-- **The multiplication `Ω^p_{X/S} × Ω^c_{X/S} ⟶ Ω^{p+c}_{X/S}`** of the sheaf of graded algebras
of relative differential forms, in the two degrees the pairing of [Stacks, Tag 0G88] pairs.  These
are the degrees of the global-equation pairing
`AlgebraicGeometry.Scheme.Hom.formSupportWedgePair`, so no transport of degrees occurs inside the
pairing.  A reducible abbreviation, so that `rw` sees through it. -/
abbrev formWedgePair (π : X ⟶ S) (p c : ℕ) :
    SheafOfModules.BilinearMap (relativeDifferentialForms π (p : ℤ))
      (relativeDifferentialForms π (c : ℤ))
      (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))) :=
  (relativeDifferentialFormsAlgebra π).mul (p : ℤ) (c : ℤ)

variable (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {c : ℕ} (p : ℕ)

/-- **Multiplication by a section `ω` of `Ω^p_{X/S}` over `V`, as a morphism of the restrictions
to `V`.**  A section over `V` is a global section of the restriction to `V`, by
`Stacks.Gysin.localSections`, and multiplication by a global section is
`Stacks.Cohomology.rightMulHom` of the restricted multiplication. -/
def localFormWedgeHom (V : X.Opens) (ω : Γ(relativeDifferentialForms π (p : ℤ), V)) :
    (Scheme.Modules.restrictFunctor V.ι).obj
        (relativeDifferentialForms π (c : ℤ)) ⟶
      (Scheme.Modules.restrictFunctor V.ι).obj
        (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))) :=
  Stacks.Cohomology.rightMulHom (restrictBilinear V.ι (formWedgePair π p c)).flip
    (localSections V (relativeDifferentialForms π (p : ℤ)) ω)

/-- **Multiplication by `ω` on a local section**, in the shape
`Stacks.Cohomology.rightMulHom_app_apply` delivers it. -/
theorem localFormWedgeHom_val_app_aux (V : X.Opens)
    (ω : Γ(relativeDifferentialForms π (p : ℤ), V)) (U : V.toScheme.Opens)
    (y : ((Scheme.Modules.restrictFunctor V.ι).obj
      (relativeDifferentialForms π (c : ℤ))).val.obj (op U)) :
    (localFormWedgeHom π p V ω).val.app (op U) y =
      (restrictBilinear V.ι (formWedgePair π p c)).flip.app (op U) y
        ((localSections V (relativeDifferentialForms π (p : ℤ)) ω).eval (op U)) :=
  Stacks.Cohomology.rightMulHom_app_apply
    (restrictBilinear V.ι (formWedgePair π p c)).flip
    (localSections V (relativeDifferentialForms π (p : ℤ)) ω) (op U) y

/-- **Multiplication by `ω` on a local section**: the wedge of the restriction of `ω` with the
section.  Proved by a chain of the three rewriting lemmas rather than by one `rfl`. -/
theorem localFormWedgeHom_val_app (V : X.Opens)
    (ω : Γ(relativeDifferentialForms π (p : ℤ), V)) (U : V.toScheme.Opens)
    (y : ((Scheme.Modules.restrictFunctor V.ι).obj
      (relativeDifferentialForms π (c : ℤ))).val.obj (op U)) :
    (localFormWedgeHom π p V ω).val.app (op U) y =
      (formWedgePair π p c).app (op (V.ι ''ᵁ U))
        ((relativeDifferentialForms π (p : ℤ)).presheaf.map
          (homOfLE (Scheme.Opens.ι_image_le V U)).op ω) y := by
  refine Eq.trans (localFormWedgeHom_val_app_aux π p V ω U y) ?_
  rfl

/-- **Multiplication by a section over `V`, read as a morphism of sheaves on the whole of `X`**
whose target is the direct image of the restriction to `V`.  Its restriction to `V` is
multiplication by `ω` again, by `Stacks.Gysin.restrictFunctor_map_openUnit_comp`, and being a
morphism of sheaves on `X` it is automatically compatible with restriction to every open — which
is what carries the pairing's naturality. -/
def localFormWedgeExt (V : X.Opens) (ω : Γ(relativeDifferentialForms π (p : ℤ), V)) :
    relativeDifferentialForms π (c : ℤ) ⟶
      (Scheme.Modules.pushforward V.ι).obj ((Scheme.Modules.restrictFunctor V.ι).obj
        (relativeDifferentialForms π ((p : ℤ) + (c : ℤ)))) :=
  openUnit V (relativeDifferentialForms π (c : ℤ)) ≫
    (Scheme.Modules.pushforward V.ι).map (localFormWedgeHom π p V ω)

/-! ### The excision, read as a conjugation -/

/-- The derived excision of [Stacks, Tag 0G78] conjugates the degree-`n` local cohomology functor
of an open subscheme into the restriction of the one of the ambient scheme.  This is
`Stacks.Gysin.supportCohomologyRestrictIso_naturality` solved for the restricted map. -/
theorem restrictFunctor_map_supportCohomologySheafFunctor (V : X.Opens) {T : Set X}
    (hT : IsClosed T) (hTV : IsClosed (V.ι ⁻¹' T)) (n : ℤ) {M N : X.Modules} (φ : M ⟶ N) :
    (Scheme.Modules.restrictFunctor V.ι).map ((supportCohomologySheafFunctor hT n).map φ) =
      ((supportCohomologyRestrictIso V hT hTV n M).hom ≫
          (supportCohomologySheafFunctor hTV n).map
            ((Scheme.Modules.restrictFunctor V.ι).map φ)) ≫
        (supportCohomologyRestrictIso V hT hTV n N).inv := by
  rw [supportCohomologySheafFunctor_map, supportCohomologySheafFunctor_map]
  exact (Iso.eq_comp_inv _).mpr (supportCohomologyRestrictIso_naturality V hT hTV n φ)

/-! ### The pairing over an open -/

/-- **The target `i_*ℋ^c_Z(Ω^{p+c}_{X/S})` of the Gysin map, in the spelling the derived excision
is stated at.**  This is `Stacks.Gysin.gysinTarget i π c p` — `conormalTarget_eq` — but it is
a reducible abbreviation, so a statement mixing it with the excision stays type-correct at
`implicit` transparency.  The route from `gysinTarget` to this spelling passes through
`CategoryTheory.Limits.getColimitCocone`, which is not exposed, and `rw` cannot see through it. -/
abbrev conormalTarget (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) (c p : ℕ) : X.Modules :=
  (supportCohomologySheafFunctor (isClosed_range_base i) (c : ℤ)).obj
    (relativeDifferentialForms π ((p : ℤ) + (c : ℤ)))

/-- The target `conormalTarget i π c p` is `Stacks.Gysin.gysinTarget i π c p`. -/
theorem conormalTarget_eq : conormalTarget i π c p = gysinTarget i π c p := rfl

/-- **The second factor `i_*ℋ^c_Z(Ω^c_{X/S})` of the pairing of [Stacks, Tag 0G88]**, in the same
degree `c` the global-equation pairing
`AlgebraicGeometry.Scheme.Hom.formSupportWedgePair` uses.  It is *not*
`Stacks.Gysin.gysinTarget i π c 0`, whose coefficient sheaf has the degree written `0 + c`;
`Stacks.Gysin.gysinDegreeShift` is the comparison, and it is applied to the Gysin map of
[Stacks, Tag 0G86] at `p = 0` rather than carried through the pairing, so that no `eqToHom` occurs
inside the pairing itself. -/
abbrev conormalSource (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) (c : ℕ) : X.Modules :=
  (supportCohomologySheafFunctor (isClosed_range_base i) (c : ℤ)).obj
    (relativeDifferentialForms π (c : ℤ))

/-- **The wedge pairing over an open `V`, as a morphism of the restrictions to `V`**: the derived
excision, multiplication by `ω` on the restrictions, and the derived excision back.  No family of
equations occurs. -/
def conormalWedgeHom (V : X.Opens) (ω : Γ(relativeDifferentialForms π (p : ℤ), V)) :
    Scheme.Modules.restrict (conormalSource i π c) V.ι ⟶
      Scheme.Modules.restrict (conormalTarget i π c p) V.ι :=
  ((supportCohomologyRestrictIso V (isClosed_range_base i) (isClosed_preimage_range_base i V)
          (c : ℤ)
          (relativeDifferentialForms π (c : ℤ))).hom ≫
      (supportCohomologySheafFunctor (isClosed_preimage_range_base i V) (c : ℤ)).map
        (localFormWedgeHom π p V ω)) ≫
    (supportCohomologyRestrictIso V (isClosed_range_base i) (isClosed_preimage_range_base i V)
      (c : ℤ) (relativeDifferentialForms π ((p : ℤ) + (c : ℤ)))).inv

/-- **The value of the wedge pairing on the sections over an open `V`.** -/
def conormalWedgeVal (V : X.Opens) (ω : Γ(relativeDifferentialForms π (p : ℤ), V))
    (t : Γ(conormalSource i π c, V)) : Γ(conormalTarget i π c p, V) :=
  restrictSections (conormalWedgeHom i π p V ω) V le_rfl t

/-! ### The characterisation by the unit of the restriction adjunction -/

/-- **The pairing's value is characterised by multiplication by `ω` read on the whole of `X`.**
Both sides are morphisms of sheaves on `X` applied to sections, which is what makes the pairing's
compatibility with restriction formal.

The proof is the derived excision's naturality in the coefficient module twice, after which both
sides are the excision conjugate of `localFormWedgeHom` followed by the excision conjugate of the
unit; the unit absorbs the direct image of `localFormWedgeHom` by
`Stacks.Gysin.restrictFunctor_map_openUnit_comp`. -/
theorem restrictFunctor_map_supportCohomology_localFormWedgeExt (V : X.Opens)
    (ω : Γ(relativeDifferentialForms π (p : ℤ), V)) :
    (Scheme.Modules.restrictFunctor V.ι).map
        ((supportCohomologySheafFunctor (isClosed_range_base i) (c : ℤ)).map
          (localFormWedgeExt π p V ω)) =
      conormalWedgeHom i π p V ω ≫
        (Scheme.Modules.restrictFunctor V.ι).map
          ((supportCohomologySheafFunctor (isClosed_range_base i) (c : ℤ)).map
            (openUnit V (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))))) := by
  refine Eq.trans (restrictFunctor_map_supportCohomologySheafFunctor V (isClosed_range_base i)
    (isClosed_preimage_range_base i V) (c : ℤ) (localFormWedgeExt π p V ω)) ?_
  refine Eq.trans ?_ (congrArg (fun ψ => conormalWedgeHom i π p V ω ≫ ψ)
    (restrictFunctor_map_supportCohomologySheafFunctor V (isClosed_range_base i)
      (isClosed_preimage_range_base i V) (c : ℤ)
      (openUnit V (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))))).symm)
  simp only [localFormWedgeExt]
  rw [restrictFunctor_map_openUnit_comp, CategoryTheory.Functor.map_comp]
  simp only [conormalWedgeHom]
  simp only [Category.assoc]
  simp only [Iso.inv_hom_id_assoc]

/-- The characterisation of `conormalWedgeVal`, on the sections over an open of `V`. -/
theorem supportCohomology_localFormWedgeExt_app (V : X.Opens)
    (ω : Γ(relativeDifferentialForms π (p : ℤ), V)) (V' : X.Opens) (hV' : V' ≤ V)
    (t : Γ(conormalSource i π c, V')) :
    ((supportCohomologySheafFunctor (isClosed_range_base i) (c : ℤ)).map
          (localFormWedgeExt π p V ω)).app V' t =
      ((supportCohomologySheafFunctor (isClosed_range_base i) (c : ℤ)).map
          (openUnit V (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))))).app V'
        (restrictSections (conormalWedgeHom i π p V ω) V' hV' t) := by
  refine Eq.trans (restrictSections_restrictFunctor_map V
    ((supportCohomologySheafFunctor (isClosed_range_base i) (c : ℤ)).map
      (localFormWedgeExt π p V ω)) V' hV' t).symm ?_
  rw [restrictFunctor_map_supportCohomology_localFormWedgeExt (c := c) i π p V ω,
    restrictSections_comp]
  exact restrictSections_restrictFunctor_map V _ V' hV' _


/-! ### The pairing on sections, computed -/

/-- The direct image of a morphism of restrictions, on sections. -/
theorem pushforward_map_app (V : X.Opens) {M N : V.toScheme.Modules} (ψ : M ⟶ N)
    (U : X.Opens) (m : ((Scheme.Modules.pushforward V.ι).obj M).val.obj (op U)) :
    ((Scheme.Modules.pushforward V.ι).map ψ).val.app (op U) m =
      ψ.val.app (op (V.ι ⁻¹ᵁ U)) m :=
  rfl

/-- The unit of the restriction adjunction, on sections, in the `· .val.app` spelling. -/
theorem openUnit_val_app (V : X.Opens) (M : X.Modules) (U : X.Opens) (m : M.val.obj (op U)) :
    (openUnit V M).val.app (op U) m =
      M.val.map (homOfLE (V.ι.image_preimage_le U)).op m :=
  rfl

/-- Restricting a section along two nested inclusions of opens is restricting it along the
composite. -/
private theorem val_map_comp_self {M : X.Modules} {A B C : X.Opens} (h₁ : B ≤ A) (h₂ : C ≤ B)
    (h₃ : C ≤ A) (m : M.val.obj (op A)) :
    M.val.map (homOfLE h₂).op (M.val.map (homOfLE h₁).op m) = M.val.map (homOfLE h₃).op m := by
  rw [← PresheafOfModules.map_comp_apply]
  exact PresheafOfModules.congr_map_apply M.val (Subsingleton.elim _ _) m

/-- **Multiplication by `ω`, on the sections over an open of `V`**: the wedge of the restriction
of `ω` with the given section. -/
theorem restrictSections_localFormWedgeHom (V : X.Opens)
    (ω : Γ(relativeDifferentialForms π (p : ℤ), V)) (U : X.Opens) (hU : U ≤ V)
    (m : Γ(relativeDifferentialForms π (c : ℤ), U)) :
    restrictSections (localFormWedgeHom π p V ω) U hU m =
      (formWedgePair π p c).app (op U)
        ((relativeDifferentialForms π (p : ℤ)).val.map (homOfLE hU).op ω) m := by
  rw [restrictSections_apply]
  refine Eq.trans (congrArg
    ((relativeDifferentialForms π ((p : ℤ) + (c : ℤ))).val.map
      (homOfLE (image_preimage_of_le hU).ge).op)
    (localFormWedgeHom_val_app π p V ω (V.ι ⁻¹ᵁ U) _)) ?_
  refine Eq.trans
    ((formWedgePair π p c).naturality (homOfLE (image_preimage_of_le hU).ge).op _ _) ?_
  refine congrArg₂ (fun x y => (formWedgePair π p c).app (op U) x y) ?_ ?_
  · exact val_map_comp_self (Scheme.Opens.ι_image_le V (V.ι ⁻¹ᵁ U))
      (image_preimage_of_le hU).ge hU ω
  · exact val_map_homOfLE_self (image_preimage_of_le hU).le (image_preimage_of_le hU).ge m

/-- **Multiplication by `ω` read on the whole of `X`, on the sections over an open of `V`**: the
wedge, followed by the restriction the unit performs.  This is the naturality of the
multiplication of forms. -/
theorem localFormWedgeExt_val_app (V : X.Opens) (ω : Γ(relativeDifferentialForms π (p : ℤ), V))
    (U : X.Opens) (hU : U ≤ V)
    (m : Γ(relativeDifferentialForms π (c : ℤ), U)) :
    (localFormWedgeExt π p V ω).val.app (op U) m =
      (openUnit V (relativeDifferentialForms π ((p : ℤ) + (c : ℤ)))).val.app (op U)
        ((formWedgePair π p c).app (op U)
          ((relativeDifferentialForms π (p : ℤ)).val.map (homOfLE hU).op ω) m) := by
  have hsplit : (localFormWedgeExt π p V ω).val.app (op U) =
      (openUnit V (relativeDifferentialForms π (c : ℤ))).val.app (op U) ≫
        ((Scheme.Modules.pushforward V.ι).map (localFormWedgeHom π p V ω)).val.app (op U) :=
    PresheafOfModules.comp_app _ _ (op U)
  rw [hsplit]
  refine Eq.trans (pushforward_map_app V (localFormWedgeHom π p V ω) U
    ((openUnit V (relativeDifferentialForms π (c : ℤ))).val.app (op U) m)) ?_
  refine Eq.trans (localFormWedgeHom_val_app π p V ω (V.ι ⁻¹ᵁ U) _) ?_
  refine Eq.trans ?_ (openUnit_val_app V
    (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))) U
    ((formWedgePair π p c).app (op U)
      ((relativeDifferentialForms π (p : ℤ)).val.map (homOfLE hU).op ω) m)).symm
  refine Eq.trans ?_ ((formWedgePair π p c).naturality
    (homOfLE (V.ι.image_preimage_le U)).op
    ((relativeDifferentialForms π (p : ℤ)).val.map (homOfLE hU).op ω) m).symm
  exact congrArg₂ (fun x y => (formWedgePair π p c).app (op (V.ι ''ᵁ (V.ι ⁻¹ᵁ U))) x y)
    (val_map_comp_self hU (V.ι.image_preimage_le U)
      (Scheme.Opens.ι_image_le V (V.ι ⁻¹ᵁ U)) ω).symm
    (openUnit_val_app V (relativeDifferentialForms π (c : ℤ)) U m)

/-! ### Multiplication by a section over `V`, restricted to a smaller open -/

/-- **Multiplication by `ω` read on the whole of `X`, restricted to an open `W ≤ V`**: it is
multiplication by `ω|_W` followed by the restriction to `W` of the unit of `V`.  For `W = V` this
is `Stacks.Gysin.restrictFunctor_map_openUnit_comp`; the general case is proved on sections, where
every step is the naturality of the multiplication of forms and the only transport is the
restriction of `ω` along `W.ι ''ᵁ U' ≤ W ≤ V`. -/
theorem restrictFunctor_map_localFormWedgeExt {V W : X.Opens} (hWV : W ≤ V)
    (ω : Γ(relativeDifferentialForms π (p : ℤ), V)) :
    (Scheme.Modules.restrictFunctor W.ι).map (localFormWedgeExt π p V ω) =
      localFormWedgeHom π p W
          ((relativeDifferentialForms π (p : ℤ)).val.map (homOfLE hWV).op ω) ≫
        (Scheme.Modules.restrictFunctor W.ι).map
          (openUnit V (relativeDifferentialForms π ((p : ℤ) + (c : ℤ)))) := by
  refine Scheme.Modules.hom_ext _ _ fun U' => ?_
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun m => ?_)
  refine Eq.trans (restrictFunctor_map_val_app W (localFormWedgeExt π p V ω) U' m) ?_
  refine Eq.trans (localFormWedgeExt_val_app π p V ω (W.ι ''ᵁ U')
    ((Scheme.Opens.ι_image_le W U').trans hWV) m) ?_
  refine Eq.trans ?_ (restrictFunctor_map_val_app W
    (openUnit V (relativeDifferentialForms π ((p : ℤ) + (c : ℤ)))) U'
    ((localFormWedgeHom π p W
      ((relativeDifferentialForms π (p : ℤ)).val.map (homOfLE hWV).op ω)).val.app (op U') m)).symm
  refine congrArg
    ((openUnit V (relativeDifferentialForms π ((p : ℤ) + (c : ℤ)))).val.app
      (op (W.ι ''ᵁ U'))) ?_
  refine Eq.trans ?_ (localFormWedgeHom_val_app π p W
    ((relativeDifferentialForms π (p : ℤ)).val.map (homOfLE hWV).op ω) U' m).symm
  exact congrArg (fun x => (formWedgePair π p c).app (op (W.ι ''ᵁ U')) x m)
    (val_map_comp_self hWV (Scheme.Opens.ι_image_le W U')
      ((Scheme.Opens.ι_image_le W U').trans hWV) ω).symm

/-- **The comparison of the units carries multiplication by `ω` to multiplication by `ω|_W`.**
The transpose of the left-hand side under the restriction adjunction of `W` is the restriction of
`localFormWedgeExt` followed by the inverse of the restricted unit of `V`, which is
multiplication by `ω|_W` by `restrictFunctor_map_localFormWedgeExt`; and the transpose of a unit
composed with a direct image is that direct image's morphism. -/
theorem localFormWedgeExt_comp_openUnitTransport {V W : X.Opens} (hWV : W ≤ V)
    (ω : Γ(relativeDifferentialForms π (p : ℤ), V)) :
    localFormWedgeExt π p V ω ≫
        openUnitTransport hWV (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))) =
      localFormWedgeExt π p W
        ((relativeDifferentialForms π (p : ℤ)).val.map (homOfLE hWV).op ω) := by
  have := isIso_restrictFunctor_map_openUnit hWV
    (relativeDifferentialForms π ((p : ℤ) + (c : ℤ)))
  refine Eq.trans ((Scheme.Modules.restrictAdjunction W.ι).homEquiv_naturality_left
    (localFormWedgeExt π p V ω)
    (inv ((Scheme.Modules.restrictFunctor W.ι).map
      (openUnit V (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))))))).symm ?_
  have hcancel : (Scheme.Modules.restrictFunctor W.ι).map (localFormWedgeExt π p V ω) ≫
      inv ((Scheme.Modules.restrictFunctor W.ι).map
        (openUnit V (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))))) =
      localFormWedgeHom π p W
        ((relativeDifferentialForms π (p : ℤ)).val.map (homOfLE hWV).op ω) := by
    rw [restrictFunctor_map_localFormWedgeExt (c := c) π p hWV ω, Category.assoc,
      IsIso.hom_inv_id, Category.comp_id]
  refine Eq.trans (congrArg ((Scheme.Modules.restrictAdjunction W.ι).homEquiv _ _) hcancel) ?_
  exact (Scheme.Modules.restrictAdjunction W.ι).homEquiv_unit _ _ _

/-! ### The excision conjugate of the unit is invertible after restriction -/

/-- **The excision conjugate of the unit of `W` becomes invertible after restriction to `W`.**
Restriction carries `i_*ℋ^c_Z` of a morphism to `i_*ℋ^c_Z` of the restricted morphism, up to the
excision, by `restrictFunctor_map_supportCohomologySheafFunctor`; and the restriction of the unit
of `W` to `W` is invertible. -/
theorem isIso_restrictFunctor_map_supportCohomology_openUnit (W : X.Opens) {T : Set X}
    (hT : IsClosed T) (hTW : IsClosed (W.ι ⁻¹' T)) (n : ℤ) (M : X.Modules) :
    IsIso ((Scheme.Modules.restrictFunctor W.ι).map
      ((supportCohomologySheafFunctor hT n).map (openUnit W M))) := by
  have := isIso_restrictFunctor_map_openUnit_self W M
  rw [restrictFunctor_map_supportCohomologySheafFunctor W hT hTW n (openUnit W M)]
  infer_instance

/-- `restrictSections` of the identity is the identity. -/
theorem restrictSections_id {M : X.Modules} {O : X.Opens} (U : X.Opens) (h : U ≤ O)
    (m : Γ(M, U)) :
    restrictSections (𝟙 (Scheme.Modules.restrict M O.ι)) U h m = m := by
  rw [show (𝟙 (Scheme.Modules.restrict M O.ι)) =
      (Scheme.Modules.restrictFunctor O.ι).map (𝟙 M) from
    (CategoryTheory.Functor.map_id _ _).symm, restrictSections_restrictFunctor_map]
  rfl

/-- **An invertible morphism of restrictions is injective on sections.** -/
theorem restrictSections_injective {M N : X.Modules} {O : X.Opens}
    (θ : Scheme.Modules.restrict M O.ι ⟶ Scheme.Modules.restrict N O.ι) [IsIso θ]
    (U : X.Opens) (h : U ≤ O) {m m' : Γ(M, U)}
    (hmm : restrictSections θ U h m = restrictSections θ U h m') : m = m' := by
  have key : ∀ x : Γ(M, U),
      restrictSections (inv θ) U h (restrictSections θ U h x) = x := fun x =>
    Eq.trans (restrictSections_comp θ (inv θ) U h x).symm
      (Eq.trans (congrArg (fun ψ => restrictSections ψ U h x) (IsIso.hom_inv_id θ))
        (restrictSections_id U h x))
  exact Eq.trans (key m).symm (Eq.trans (congrArg (restrictSections (inv θ) U h) hmm) (key m'))

/-- **A morphism of sheaves of modules whose restriction to `W` is invertible is injective on the
sections over `W`.** -/
theorem app_injective_of_isIso_restrictFunctor_map {M N : X.Modules} (W : X.Opens) (φ : M ⟶ N)
    [IsIso ((Scheme.Modules.restrictFunctor W.ι).map φ)] {m m' : Γ(M, W)}
    (hmm : φ.app W m = φ.app W m') : m = m' :=
  restrictSections_injective ((Scheme.Modules.restrictFunctor W.ι).map φ) W le_rfl
    (Eq.trans (restrictSections_restrictFunctor_map W φ W le_rfl m)
      (Eq.trans hmm (restrictSections_restrictFunctor_map W φ W le_rfl m').symm))

/-- The action on sections of a functor applied to a composite, split in two.  Stated at a
variable endofunctor and explicit morphisms, so that the two concrete instances below are one
`exact` each. -/
private theorem functor_map_comp_app (A : X.Modules ⥤ X.Modules) {M N P : X.Modules}
    (α : M ⟶ N) (β : N ⟶ P) (U : X.Opens) (x : Γ(A.obj M, U)) :
    (A.map (α ≫ β)).app U x = (A.map β).app U ((A.map α).app U x) := by
  rw [A.map_comp]
  rfl

/-! ### The pairing over an open is the pairing over a smaller one -/

/-- **The pairing over `V` and the pairing over a smaller open `W` agree on the sections over
`W`.**  This is the one clause of the gluing that compares the derived excisions of two different
opens, and it is proved without any coherence of the excision: both sides are characterised
through `localFormWedgeExt` by the excision conjugate of the unit of `W`, which is injective on
the sections over `W` by `app_injective_of_isIso_restrictFunctor_map`; the two characterisations
are brought to the same shape by `localFormWedgeExt_comp_openUnitTransport` and
`openUnit_comp_openUnitTransport`. -/
theorem restrictSections_conormalWedgeHom_le {V W : X.Opens} (hWV : W ≤ V)
    (ω : Γ(relativeDifferentialForms π (p : ℤ), V)) (s : Γ(conormalSource i π c, W)) :
    restrictSections (conormalWedgeHom i π p W
          ((relativeDifferentialForms π (p : ℤ)).val.map (homOfLE hWV).op ω)) W le_rfl s =
      restrictSections (conormalWedgeHom i π p V ω) W hWV s := by
  have := isIso_restrictFunctor_map_supportCohomology_openUnit W (isClosed_range_base i)
    (isClosed_preimage_range_base i W) (c : ℤ)
    (relativeDifferentialForms π ((p : ℤ) + (c : ℤ)))
  refine app_injective_of_isIso_restrictFunctor_map W
    ((supportCohomologySheafFunctor (isClosed_range_base i) (c : ℤ)).map
      (openUnit W (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))))) ?_
  rw [← supportCohomology_localFormWedgeExt_app i π p W
      ((relativeDifferentialForms π (p : ℤ)).val.map (homOfLE hWV).op ω) W le_rfl s,
    ← localFormWedgeExt_comp_openUnitTransport π p hWV ω, functor_map_comp_app,
    supportCohomology_localFormWedgeExt_app i π p V ω W hWV s, ← functor_map_comp_app,
    openUnit_comp_openUnitTransport hWV]

/-- **Compatibility of the pairing with restriction.**  This is the `naturality` clause of the
local data the gluing consumes, and it mentions no equations. -/
theorem conormalWedgeVal_res {V W : X.Opens} (hWV : W ≤ V)
    (ω : Γ(relativeDifferentialForms π (p : ℤ), V)) (t : Γ(conormalSource i π c, V)) :
    conormalWedgeVal i π p W ((relativeDifferentialForms π (p : ℤ)).val.resLE hWV ω)
        ((conormalSource i π c).val.resLE hWV t) =
      (conormalTarget i π c p).val.resLE hWV (conormalWedgeVal i π p V ω t) :=
  Eq.trans (restrictSections_conormalWedgeHom_le i π p hWV ω
      ((conormalSource i π c).val.resLE hWV t))
    (restrictSections_res (conormalWedgeHom i π p V ω) W V hWV le_rfl t)

/-! ### Biadditivity and homogeneity in the second variable -/

/-- The pairing `conormalWedgeVal i π p V ω` is additive in its second variable. -/
theorem conormalWedgeVal_add_right (V : X.Opens)
    (ω : Γ(relativeDifferentialForms π (p : ℤ), V)) (t t' : Γ(conormalSource i π c, V)) :
    conormalWedgeVal i π p V ω (t + t') =
      conormalWedgeVal i π p V ω t + conormalWedgeVal i π p V ω t' :=
  restrictSections_add (conormalWedgeHom i π p V ω) V le_rfl t t'

/-- The pairing `conormalWedgeVal i π p V ω` commutes with multiplication by a function
`r ∈ Γ(X, V)` in its second variable. -/
theorem conormalWedgeVal_smul_right (V : X.Opens) (r : Γ(X, V))
    (ω : Γ(relativeDifferentialForms π (p : ℤ), V)) (t : Γ(conormalSource i π c, V)) :
    conormalWedgeVal i π p V ω (r • t) = r • conormalWedgeVal i π p V ω t :=
  restrictSections_smul (conormalWedgeHom i π p V ω) V le_rfl r t

/-! ### The sectionwise family of a morphism of restrictions, in the morphism

`Stacks.AlgebraicGeometry.ModuleLimits.restrictSections_add` and `restrictSections_smul` are the
two laws of `restrictSections θ U h m` in the *section* `m`.  The two laws of the pairing in its
first variable are laws in the *morphism* `θ`, because that is where `ω` sits, and the three
results here supply them: additivity in `θ`, and the value of multiplication by a function on the
chart, which is what a scalar does to `θ`. -/

/-- **The action on sections of a sum of two morphisms of restrictions is the sum of their
actions**, on the sections over the image of an open of the chart.  A morphism of sheaves of
modules acts additively in itself, and the two conjugating isomorphisms of `restrictHomApp` are
additive because the category is preadditive. -/
theorem restrictHomApp_add {M N : X.Modules} {O : X.Opens}
    (θ θ' : Scheme.Modules.restrict M O.ι ⟶ Scheme.Modules.restrict N O.ι)
    (U' : O.toScheme.Opens) (m : Γ(M, O.ι ''ᵁ U')) :
    restrictHomApp (θ + θ') U' m = restrictHomApp θ U' m + restrictHomApp θ' U' m := by
  unfold restrictHomApp
  simp only [ConcreteCategory.comp_apply]
  rw [Scheme.Modules.Hom.add_app]
  rfl

/-- **The sectionwise family of a sum of two morphisms of restrictions is the sum of their
sectionwise families.**  Arbitrary sheaves of modules, arbitrary open, arbitrary section: the
companion of `Stacks.AlgebraicGeometry.ModuleLimits.restrictSections_add`, which is the same law
in the section rather than in the morphism. -/
theorem restrictSections_add_hom {M N : X.Modules} {O : X.Opens}
    (θ θ' : Scheme.Modules.restrict M O.ι ⟶ Scheme.Modules.restrict N O.ι)
    (U : X.Opens) (h : U ≤ O) (m : Γ(M, U)) :
    restrictSections (θ + θ') U h m = restrictSections θ U h m + restrictSections θ' U h m := by
  unfold restrictSections
  rw [restrictHomApp_add, map_add]

/-- **Multiplication by a function on the chart acts on sections by multiplication by that
function**, on the sections over the image of an open of the chart.  The scalar crosses the
identification `AlgebraicGeometry.Scheme.Modules.restrictAppIso` of the two readings of the
sections by `AlgebraicGeometry.Scheme.Modules.smul_restrictAppIso_hom_apply`, and the comparison
of the two readings of the *functions* is the identity for the inclusion of an open, by
`AlgebraicGeometry.Scheme.Opens.ι_appIso`. -/
theorem restrictHomApp_globalSmul {M : X.Modules} (O : X.Opens) (a : Γ(O.toScheme, ⊤))
    (U' : O.toScheme.Opens) (m : Γ(M, O.ι ''ᵁ U')) :
    restrictHomApp (AlgebraicGeometry.globalSmul a (Scheme.Modules.restrict M O.ι)) U' m =
      (show Γ(X, O.ι ''ᵁ U') from
        O.toScheme.presheaf.map (homOfLE (show U' ≤ ⊤ from le_top)).op a) • m := by
  unfold restrictHomApp
  simp only [ConcreteCategory.comp_apply]
  rw [AlgebraicGeometry.globalSmul_app, Scheme.Modules.smul_restrictAppIso_hom_apply,
    Iso.inv_hom_id_apply, Scheme.Opens.ι_appIso, Iso.refl_inv]
  rfl

/-- **The sectionwise family of multiplication by a function on the chart is multiplication by
that function**, read on the open of the ambient scheme by
`Stacks.Gysin.chartScalar`. -/
theorem restrictSections_globalSmul {M : X.Modules} (O : X.Opens) (a : Γ(O.toScheme, ⊤))
    (U : X.Opens) (h : U ≤ O) (m : Γ(M, U)) :
    restrictSections (AlgebraicGeometry.globalSmul a (Scheme.Modules.restrict M O.ι)) U h m =
      chartScalar O h a • m := by
  unfold restrictSections
  rw [restrictHomApp_globalSmul, Scheme.Modules.map_smul, modules_presheaf_map_homOfLE_self]
  rfl

/-- **A function on an open, read as a function on the open subscheme and brought back to a
smaller open, is its own restriction.**  The generalisation of
`Stacks.Gysin.chartScalar_self` to an open properly contained in the chart; all three maps are
restriction maps of `𝒪_X` between opens of `X`. -/
theorem chartScalar_restrictScalarHom (V : X.Opens) {U : X.Opens} (hU : U ≤ V) (r : Γ(X, V)) :
    chartScalar V hU (restrictScalarHom V r) = X.presheaf.map (homOfLE hU).op r := by
  change X.presheaf.map _ (V.toScheme.presheaf.map _ (X.presheaf.map _ r)) = _
  refine Eq.trans (presheaf_map_comp_apply _ _ _) ?_
  refine Eq.trans (presheaf_map_comp_apply _ _ r) ?_
  exact presheaf_map_congr _ _ r

/-! ### The two laws in the first variable, with no equations

Multiplication by `ω` on the restrictions to `V` is additive and `𝒪`-homogeneous in `ω` because
the multiplication of forms is a bilinear map; the degree-`c` local cohomology functor of `V` is
additive and `Γ(V, ⊤)`-linear on morphisms by
`Stacks.Perfect.SupportCohomologyLinear.supportCohomologySheafFunctor_additive` and
`supportCohomologySheafFunctor_linear`; and conjugating by the derived excision preserves both,
the category being preadditive and `Γ(V, ⊤)`-linear.  **No family of equations occurs anywhere in
this section**, so the two laws hold over *every* open and at *every* conormal rank, `c = 0`
included — where no family of `c` equations cutting out `Z` exists on an open meeting the
complement of `Z` and the equation route is unavailable. -/

/-- **Multiplication by a section of `Ω^p_{X/S}` over `V` is additive in that section.** -/
theorem localFormWedgeHom_add (V : X.Opens)
    (ω ω' : Γ(relativeDifferentialForms π (p : ℤ), V)) :
    localFormWedgeHom π p (c := c) V (ω + ω') =
      localFormWedgeHom π p (c := c) V ω + localFormWedgeHom π p (c := c) V ω' := by
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun y => ?_)
  change (localFormWedgeHom π p (c := c) V (ω + ω')).val.app (op U) y =
    (localFormWedgeHom π p (c := c) V ω).val.app (op U) y +
      (localFormWedgeHom π p (c := c) V ω').val.app (op U) y
  refine Eq.trans (localFormWedgeHom_val_app π p V (ω + ω') U y)
    (Eq.trans ?_ (congrArg₂ (fun a b => a + b)
      (localFormWedgeHom_val_app π p V ω U y).symm
      (localFormWedgeHom_val_app π p V ω' U y).symm))
  rw [map_add]
  exact (formWedgePair π p c).map_add_left _ _ _ y

/-- **Multiplication by a section of `Ω^p_{X/S}` over `V` is homogeneous in that section**: the
scalar `r ∈ Γ(X, V)`, read as a global function on `V.toScheme` by
`Stacks.Gysin.restrictScalarHom`, passes to the `Γ(V, ⊤)`-module structure on the morphisms of
sheaves of modules on `V.toScheme`.

Checked on the sectionwise families, where every scalar is a function on an open of the *ambient*
scheme: `Stacks.Gysin.restrictSections_globalSmul` evaluates the scalar multiple of a morphism
and `chartScalar_restrictScalarHom` brings the function back. -/
theorem localFormWedgeHom_smul (V : X.Opens) (r : Γ(X, V))
    (ω : Γ(relativeDifferentialForms π (p : ℤ), V)) :
    localFormWedgeHom π p (c := c) V (r • ω) =
      restrictScalarHom V r • localFormWedgeHom π p (c := c) V ω := by
  refine restrictSections_ext fun U hU m => ?_
  rw [AlgebraicGeometry.smul_hom_def, restrictSections_comp, restrictSections_globalSmul,
    chartScalar_restrictScalarHom, restrictSections_smul, restrictSections_localFormWedgeHom,
    restrictSections_localFormWedgeHom]
  refine Eq.trans (congrArg (fun z => (formWedgePair π p c).app (op U) z m)
    ((relativeDifferentialForms π (p : ℤ)).val.map_smul (homOfLE hU).op r ω)) ?_
  exact (formWedgePair π p c).map_smul_left _ _ _ m

/-- **The pairing over `V` is additive in its first variable.**  The local cohomology functor of
`V` is additive on morphisms, and the two conjugating excisions are composition. -/
theorem conormalWedgeHom_add (V : X.Opens)
    (ω ω' : Γ(relativeDifferentialForms π (p : ℤ), V)) :
    conormalWedgeHom i π p (c := c) V (ω + ω') =
      conormalWedgeHom i π p (c := c) V ω + conormalWedgeHom i π p (c := c) V ω' := by
  let : (supportCohomologySheafFunctor (isClosed_preimage_range_base i V) (c : ℤ)).Additive :=
    Stacks.Perfect.SupportCohomologyLinear.supportCohomologySheafFunctor_additive
      (isClosed_preimage_range_base i V) c
  unfold conormalWedgeHom
  rw [localFormWedgeHom_add, CategoryTheory.Functor.map_add, Preadditive.comp_add,
    Preadditive.add_comp]

/-- **The pairing over `V` is homogeneous in its first variable.**  The local cohomology functor
of `V` is `Γ(V, ⊤)`-linear on morphisms, and the category of sheaves of modules on `V.toScheme`
is `Γ(V, ⊤)`-linear, so the scalar passes through the two conjugating excisions. -/
theorem conormalWedgeHom_smul (V : X.Opens) (r : Γ(X, V))
    (ω : Γ(relativeDifferentialForms π (p : ℤ), V)) :
    conormalWedgeHom i π p (c := c) V (r • ω) =
      restrictScalarHom V r • conormalWedgeHom i π p (c := c) V ω := by
  let : (supportCohomologySheafFunctor (isClosed_preimage_range_base i V) (c : ℤ)).Additive :=
    Stacks.Perfect.SupportCohomologyLinear.supportCohomologySheafFunctor_additive
      (isClosed_preimage_range_base i V) c
  let : Functor.Linear ↥Γ(V.toScheme, ⊤)
      (supportCohomologySheafFunctor (isClosed_preimage_range_base i V) (c : ℤ)) :=
    Stacks.Perfect.SupportCohomologyLinear.supportCohomologySheafFunctor_linear
      (isClosed_preimage_range_base i V) c
  unfold conormalWedgeHom
  rw [localFormWedgeHom_smul, CategoryTheory.Functor.map_smul,
    Linear.comp_smul (R := ↥Γ(V.toScheme, ⊤)) (C := V.toScheme.Modules),
    Linear.smul_comp (R := ↥Γ(V.toScheme, ⊤)) (C := V.toScheme.Modules)]

/-- **The pairing is additive in the first variable**, over every open and at every conormal
rank. -/
theorem conormalWedgeVal_add_left (V : X.Opens)
    (ω ω' : Γ(relativeDifferentialForms π (p : ℤ), V)) (t : Γ(conormalSource i π c, V)) :
    conormalWedgeVal i π p V (ω + ω') t =
      conormalWedgeVal i π p V ω t + conormalWedgeVal i π p V ω' t := by
  unfold conormalWedgeVal
  rw [conormalWedgeHom_add, restrictSections_add_hom]

/-- **The pairing is `𝒪_X`-homogeneous in the first variable**, over every open and at every
conormal rank. -/
theorem conormalWedgeVal_smul_left (V : X.Opens) (r : Γ(X, V))
    (ω : Γ(relativeDifferentialForms π (p : ℤ), V)) (t : Γ(conormalSource i π c, V)) :
    conormalWedgeVal i π p V (r • ω) t = r • conormalWedgeVal i π p V ω t := by
  unfold conormalWedgeVal
  rw [conormalWedgeHom_smul, AlgebraicGeometry.smul_hom_def, restrictSections_comp,
    restrictSections_globalSmul, chartScalar_self, restrictSections_smul]

/-! ### The pairing -/

/-- **The equation charts cover the ambient scheme**, from the hypotheses of [Stacks, Tag 0G86]
at a *positive* conormal rank: a closed immersion of finite presentation whose conormal sheaf is
locally free of rank `d + 1`.  These are the charts `Stacks.Gysin.exists_gysinCharts` produces,
read as `EquationChart`s.

At rank `0` the statement is **false** — the charts then cover only the image of `i`, an empty
family of equations cutting out `Z` on an open forcing that open into `Z` — and the covering to
use there is `Stacks.Gysin.equationChart_option_cover`, the charts augmented by the complement of
the image. -/
theorem iSup_equationChart_ambient (i : Z ⟶ X) [IsClosedImmersion i]
    [LocallyOfFinitePresentation i] {d : ℕ}
    (hE : Stacks.AlgebraicGeometry.ConormalEquations.ConormalRank i (d + 1)) :
    ⨆ a : EquationChart i (d + 1), a.ambient = ⊤ := by
  obtain ⟨ambient, equations, hvanish, hcover, _, hgen, _⟩ :=
    exists_gysinCharts i (d + 1) hE (Nat.succ_ne_zero d)
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨a, ha⟩ := hcover x
  exact TopologicalSpace.Opens.mem_iSup.mpr
    ⟨⟨ambient a, equations a, hgen a, hvanish a⟩, ha⟩

/-- **The wedge pairing `Ω^p_{X/S} × i_*ℋ^c_Z(Ω^c_{X/S}) ⟶ i_*ℋ^c_Z(Ω^{p+c}_{X/S})` of
[Stacks, Tag 0G88] at the generality of [Stacks, Tag 0G86]** — the multiplication of Cohomology,
Remark [Stacks, Tag 0G75] in the degrees the tag uses.

Its value on the sections over an open is `Stacks.Gysin.conormalWedgeVal`, by
`conormalWedgePair_app`.  **No family of equations and no hypothesis on `i` beyond closedness of
the immersion occur**: the five laws of a bilinear map are the five results above, each proved
over an arbitrary open at an arbitrary `c`, so the pairing is assembled over the one-member
covering `{⊤}` and exists at every conormal rank, `c = 0` included. -/
def conormalWedgePair (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) (c p : ℕ) :
    SheafOfModules.BilinearMap (relativeDifferentialForms π (p : ℤ))
      (conormalSource i π c) (conormalTarget i π c p) :=
  Stacks.AlgebraicGeometry.ModuleBilinearGlue.gluedBilinearMap
    (U := fun _ : PUnit.{u + 1} => (⊤ : X.Opens)) (iSup_const)
    (fun _ => Stacks.AlgebraicGeometry.ModuleBilinearGlue.localBilinearMapOfApp ⊤
      (fun V _ ω t => conormalWedgeVal i π p V ω t)
      (fun V _ ω ω' t => conormalWedgeVal_add_left i π p V ω ω' t)
      (fun V _ ω t t' => conormalWedgeVal_add_right i π p V ω t t')
      (fun V _ r ω t => conormalWedgeVal_smul_left i π p V r ω t)
      (fun V _ r ω t => conormalWedgeVal_smul_right i π p V r ω t)
      (fun _ _ _ hWV ω t => conormalWedgeVal_res i π p hWV ω t))
    (fun _ _ _ _ _ => rfl)

/-- **Over every open the pairing is the equation-free `Stacks.Gysin.conormalWedgeVal`.** -/
theorem conormalWedgePair_app (i : Z ⟶ X) [IsClosedImmersion i]
    (π : X ⟶ S) (c p : ℕ)
    (V : X.Opens) (ω : Γ(relativeDifferentialForms π (p : ℤ), V))
    (t : Γ(conormalSource i π c, V)) :
    (conormalWedgePair i π c p).app (op V) ω t = conormalWedgeVal i π p V ω t :=
  Stacks.AlgebraicGeometry.ModuleBilinearGlue.gluedBilinearMap_app
    (U := fun _ : PUnit.{u + 1} => (⊤ : X.Opens)) iSup_const _ _ PUnit.unit V le_top ω t

end Stacks.Gysin

end
