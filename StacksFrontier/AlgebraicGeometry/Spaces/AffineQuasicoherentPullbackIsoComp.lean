module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentPullbackIsoUnique
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.ExtensionByZeroUnderivedBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRepresentableBaseChangeComp
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackUnitValue
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.InverseImageIdealSheafToposComp
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.InverseImageIdealSheafToposTwoIso

/-!
# Composition coherence of the underived affine base change isomorphism

Let `U'' --h--> U' --g--> U` be morphisms of the big fppf site over `S` whose underlying schemes
are affine, with rings of global functions `R`, `R'`, `R''` and induced ring maps `φ_g : R ⟶ R'`,
`φ_h : R' ⟶ R''`.  `AlgebraicGeometry.Space.representedAffineAssociatedPullbackIso` gives, for
each of the three morphisms, an isomorphism `g^*(M^~) ≅ (R' ⊗_R M)^~` natural in the module `M`.
This file proves that the three are compatible: pasting the one of `g` with the one of `h`, and
contracting `g^* ⋙ h^*` to `(h ≫ g)^*` and `R'' ⊗_{R'} (R' ⊗_R −)` to `R'' ⊗_R −`, gives the one
of `h ≫ g`.

The proof is the reduction principle
`AlgebraicGeometry.Space.representedAffineAssociatedPullbackIso_eq_of_hom_app_self`: both sides
are isomorphisms `Φ_R ⋙ (h ≫ g)^* ≅ (R'' ⊗_R −) ⋙ Φ_{R''}`, so they agree as soon as they agree
at `M = R`, where the statement is about the structure sheaf alone.  There it is the composition
coherence of the comparison `f^*𝒪 ⟶ 𝒪'` of Stacks 03LU, which is
`AlgebraicGeometry.RingedToposHom.pullbackModulesCompIso_hom_app_comp_pullbackUnitStructureMap`
followed by its 2-isomorphism invariance
`AlgebraicGeometry.RingedToposHom.TwoIso.pullbackModulesIso_hom_app_comp_pullbackUnitStructureMap`,
together with the compatibility of `ModuleCat.extendScalarsComp` with
`ModuleCat.ExtendScalars.objSelfIso` at the base ring.

## Main definitions

* `Stacks.CategoryTheory.BaseChange.pastedBaseChangeIso`: the pasting of two base change
  isomorphisms along contractions of the two composites, in a general category-theoretic form.
* `AlgebraicGeometry.Space.representedSpacePullbackCompIso`: the contraction
  `g^* ⋙ h^* ≅ (h ≫ g)^*` of inverse images of modules along represented morphisms.
* `AlgebraicGeometry.Space.representedAffineExtendScalarsCompIso`: the contraction
  `R'' ⊗_{R'} (R' ⊗_R −) ≅ R'' ⊗_R −`.
* `AlgebraicGeometry.Space.representedAffineAssociatedPullbackCompIso`: the pasted isomorphism
  `Φ_R ⋙ (h ≫ g)^* ≅ (R'' ⊗_R −) ⋙ Φ_{R''}`.

## Main results

* `AlgebraicGeometry.Space.smallEtaleToposPullbackCompIso_inv_app_unit_comp`: the comparison
  `f^*𝒪 ⟶ 𝒪'` of Stacks 03LU is compatible with composition, across the contraction of the
  inverse images of the small étale ringed topoi.
* `AlgebraicGeometry.Space.representedAffinePullbackUnitIso_comp`: the trivialization of
  `f^*(R^~)` is compatible with composition.  This is the composition coherence at `M = R`.
* `AlgebraicGeometry.Space.representedAffineAssociatedPullbackIso_comp`: **the underived affine
  base change isomorphism is compatible with composition.**

## Implementation notes

The category-theoretic bookkeeping — the pasting, the value of the pasted isomorphism at an
object, and the two coherences — is carried out in the general section
`Stacks.CategoryTheory.BaseChange` and then instantiated, rather than rewritten in place at the
geometric spelling.  The reason is that `rw` and `simp` are unusable on the geometric goals: the
category of modules on a representable algebraic space and the category of modules on the
associated small étale ringed topos are definitionally but not reducibly equal, so a rewrite
whose motive mentions the associated-module functor followed by an inverse image of modules is
rejected as not type-correct at the transparency `rw` uses, and the `isDefEq` checks a `simp` on
such a goal performs exhaust the heartbeat budget.  At the general spelling every type is a
variable and no such check arises.

Three further spelling constraints are forced, each by a definitional unfolding that does not
terminate within the budget.

* The contraction `g^* ⋙ h^* ≅ (h ≫ g)^*` of inverse images along represented morphisms is
  `AlgebraicGeometry.Space.smallEtaleToposPullbackCompIso` followed by the renaming of the
  inverse image along `AlgebraicGeometry.Space.representedSpaceMap_comp`.  Both the renaming and
  its `congrArg` are written in the `(… ).toModulesHom.pullbackModules` dot-notation spelling of
  the inverse image of modules: at the spelling that names the two ringed topoi explicitly, the
  `eqToIso` of that `congrArg` does not elaborate within the budget.
* `AlgebraicGeometry.Space.smallEtaleToposPullbackCompIso_inv_app_unit_comp` rewrites with the
  two unit comparisons *fully instantiated* at the two morphisms of ringed topoi, as local
  hypotheses.  Rewriting with them as stated — with their ringed topoi still metavariables —
  does not match the goal after the contraction has been unfolded.
* `AlgebraicGeometry.Space.representedAffineAssociatedObjUnitIso'` is the identification of the
  associated module of `R` with the structure sheaf, retyped at the spelling that writes the
  structure sheaf as the unit of the ringed topos rather than as
  `AlgebraicGeometry.Space.structureModule`.  The two are definitionally equal, and the
  retyping is where that is checked, once, at an isomorphism of two objects; the same check
  inside an equation of composites of morphisms does not terminate within the budget.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

/-! ### Pasting two base change isomorphisms -/

namespace Stacks.CategoryTheory.BaseChange

variable {M M' M'' A B C : Type*} [Category* M] [Category* M'] [Category* M''] [Category* A]
  [Category* B] [Category* C] {Φ : M ⥤ A} {Φ' : M' ⥤ B} {Φ'' : M'' ⥤ C} {E₁ : M ⥤ M'}
  {E₂ : M' ⥤ M''} {E : M ⥤ M''} {G : A ⥤ B} {H : B ⥤ C} {K : A ⥤ C}

/-- A composite of an isomorphism with a renaming of its target along an equality of its target
with itself is that isomorphism, read on a component followed by a morphism out of it. -/
theorem trans_eqToIso_refl_inv_app_comp (c : G ⋙ H ≅ K) (e : K = K) (X : A) {T : C}
    {w : (G ⋙ H).obj X ⟶ T} {v : K.obj X ⟶ T} (hv : c.inv.app X ≫ w = v) :
    (c ≪≫ eqToIso e).inv.app X ≫ w = v := by
  rw [eqToIso_refl, Iso.trans_refl, hv]

/-- **Two base change isomorphisms, pasted.**  Given contractions `G ⋙ H ≅ K` of the two
"geometric" functors and `E₁ ⋙ E₂ ≅ E` of the two "algebraic" ones, a base change isomorphism
`Φ ⋙ G ≅ E₁ ⋙ Φ'` and a base change isomorphism `Φ' ⋙ H ≅ E₂ ⋙ Φ''` paste to a base change
isomorphism `Φ ⋙ K ≅ E ⋙ Φ''`. -/
def pastedBaseChangeIso (c : G ⋙ H ≅ K) (δ : E₁ ⋙ E₂ ≅ E) (ρ : Φ ⋙ G ≅ E₁ ⋙ Φ')
    (σ : Φ' ⋙ H ≅ E₂ ⋙ Φ'') : Φ ⋙ K ≅ E ⋙ Φ'' :=
  Functor.isoWhiskerLeft Φ c.symm ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ρ H ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft E₁ σ ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight δ Φ''

/-- The value of `Stacks.CategoryTheory.BaseChange.pastedBaseChangeIso` at an object. -/
theorem pastedBaseChangeIso_hom_app (c : G ⋙ H ≅ K) (δ : E₁ ⋙ E₂ ≅ E) (ρ : Φ ⋙ G ≅ E₁ ⋙ Φ')
    (σ : Φ' ⋙ H ≅ E₂ ⋙ Φ'') (X : M) :
    (pastedBaseChangeIso c δ ρ σ).hom.app X =
      c.inv.app (Φ.obj X) ≫ H.map (ρ.hom.app X) ≫ σ.hom.app (E₁.obj X) ≫
        Φ''.map (δ.hom.app X) := by
  simp [pastedBaseChangeIso]

/-- **A trivialization of the two base changes at a distinguished object composes.**  If the
value of the base change isomorphism of `G` at `A₁` is the comparison `ng` at `A₂` read through
the chosen isomorphisms `α`, `β`, and likewise for `H` and for the contraction `K`, then the
composition coherence for the three trivializations `ug`, `uh`, `uk` follows from the one for the
three comparisons `ng`, `nh`, `nk`.

The isomorphisms `β` cancel in the middle, and `α` is carried through the contraction by its
naturality. -/
theorem contraction_inv_app_comp_trivialization (c : G ⋙ H ≅ K) {A₁ A₂ : A} (α : A₁ ≅ A₂)
    {B₁ B₂ : B} (β : B₁ ≅ B₂) {C₁ C₂ : C} (γ : C₁ ≅ C₂) {ng : G.obj A₂ ⟶ B₂}
    {nh : H.obj B₂ ⟶ C₂} {nk : K.obj A₂ ⟶ C₂} {ug : G.obj A₁ ⟶ B₁} {uh : H.obj B₁ ⟶ C₁}
    {uk : K.obj A₁ ⟶ C₁} (hn : c.inv.app A₂ ≫ H.map ng ≫ nh = nk)
    (hug : ug = G.map α.hom ≫ ng ≫ β.inv) (huh : uh = H.map β.hom ≫ nh ≫ γ.inv)
    (huk : uk = K.map α.hom ≫ nk ≫ γ.inv) :
    c.inv.app A₁ ≫ H.map ug ≫ uh = uk := by
  subst hug huh huk
  have hnat := c.inv.naturality α.hom
  dsimp only [Functor.comp_map] at hnat
  have hcancel : H.map β.inv ≫ H.map β.hom = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]
  rw [← hn, Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hcancel, ← reassoc_of% hnat]

/-- **The pasted base change isomorphism at a distinguished object.**  Read through the
comparisons `s₁`, `s₂`, `s` of the three algebraic functors at the distinguished objects, the
value of the pasted base change isomorphism at `R` is the trivialization `uk`, provided the
contraction of the algebraic functors is compatible with the comparisons (`hδ`), the two base
change isomorphisms are normalized at the distinguished objects (`hρ`, `hσ`) and the three
trivializations satisfy the composition coherence (`hu`).

The factor `s` is absorbed into the contraction by `hδ`, the comparison `s₁` is carried across
`σ` by its naturality, and what is left is `hu`. -/
theorem pastedBaseChangeIso_hom_app_self (c : G ⋙ H ≅ K) (δ : E₁ ⋙ E₂ ≅ E)
    (ρ : Φ ⋙ G ≅ E₁ ⋙ Φ') (σ : Φ' ⋙ H ≅ E₂ ⋙ Φ'') {R : M} {R' : M'} {R'' : M''}
    {s₁ : E₁.obj R ⟶ R'} {s₂ : E₂.obj R' ⟶ R''} {s : E.obj R ⟶ R''}
    {ug : G.obj (Φ.obj R) ⟶ Φ'.obj R'} {uh : H.obj (Φ'.obj R') ⟶ Φ''.obj R''}
    {uk : K.obj (Φ.obj R) ⟶ Φ''.obj R''} (hδ : δ.hom.app R ≫ s = E₂.map s₁ ≫ s₂)
    (hρ : ρ.hom.app R ≫ Φ'.map s₁ = ug) (hσ : σ.hom.app R' ≫ Φ''.map s₂ = uh)
    (hu : c.inv.app (Φ.obj R) ≫ H.map ug ≫ uh = uk) :
    (pastedBaseChangeIso c δ ρ σ).hom.app R ≫ Φ''.map s = uk := by
  have hnat := σ.hom.naturality s₁
  dsimp only [Functor.comp_map] at hnat
  rw [pastedBaseChangeIso_hom_app, ← hu, ← hρ, ← hσ]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Φ''.map_comp (δ.hom.app R) s, hδ, Functor.map_comp, ← reassoc_of% hnat]

end Stacks.CategoryTheory.BaseChange

/-! ### Extension of scalars along a composite, at the base ring -/

namespace ModuleCat.ExtendScalars

open TensorProduct
open scoped ChangeOfRings

variable {R₁ R₂ R₃ : Type u} [CommRing R₁] [CommRing R₂] [CommRing R₃]

/-- **Extension of scalars along a composite takes the base ring to the base ring**, compatibly
with `ModuleCat.ExtendScalars.objSelfIso`: identifying `R₃ ⊗_{R₁} R₁` with
`R₃ ⊗_{R₂} (R₂ ⊗_{R₁} R₁)` and then contracting the two tensor factors in turn is the direct
identification with `R₃`.  Both sides send `1 ⊗ r` to the image of `r`.

The computation is a chain of `congrArg`s rather than a `rw` or a `simp`: the module structure
on an extension of scalars is `Module.compHom`, and a rewrite inside a tensor product across
that boundary needs a motive which is not type-correct at the transparency `rw` uses. -/
theorem objSelfIso_extendScalarsComp (f₁₂ : R₁ →+* R₂) (f₂₃ : R₂ →+* R₃) :
    (ModuleCat.extendScalarsComp f₁₂ f₂₃).hom.app (ModuleCat.of R₁ R₁) ≫
        (ModuleCat.extendScalars f₂₃).map (objSelfIso f₁₂).hom ≫ (objSelfIso f₂₃).hom =
      (objSelfIso (f₂₃.comp f₁₂)).hom := by
  refine hom_ext_one_tmul (f₂₃.comp f₁₂) fun r => ?_
  refine ((ModuleCat.comp_apply _ _ _).trans ((ModuleCat.comp_apply _ _ _).trans ?_)).trans
    (objSelfIso_hom_tmul (f₂₃.comp f₁₂) 1 r).symm
  refine (congrArg (fun y => (objSelfIso f₂₃).hom
      ((ModuleCat.extendScalars f₂₃).map (objSelfIso f₁₂).hom y))
    (ModuleCat.extendScalarsComp_hom_app_one_tmul f₁₂ f₂₃ (ModuleCat.of R₁ R₁) r)).trans ?_
  refine (congrArg (objSelfIso f₂₃).hom
    (ModuleCat.ExtendScalars.map_tmul f₂₃ (objSelfIso f₁₂).hom 1
      ((1 : R₂) ⊗ₜ[R₁, f₁₂] r))).trans ?_
  refine (congrArg (fun z => (objSelfIso f₂₃).hom ((1 : R₃) ⊗ₜ[R₂, f₂₃] z))
    (objSelfIso_hom_tmul f₁₂ (1 : R₂) r)).trans ?_
  refine (objSelfIso_hom_tmul f₂₃ (1 : R₃) ((1 : R₂) * f₁₂ r)).trans ?_
  simp

/-- `ModuleCat.ExtendScalars.objSelfIso_extendScalarsComp` read through the inverse of
`ModuleCat.extendScalarsComp`. -/
theorem objSelfIso_extendScalarsComp_inv (f₁₂ : R₁ →+* R₂) (f₂₃ : R₂ →+* R₃) :
    (ModuleCat.extendScalarsComp f₁₂ f₂₃).inv.app (ModuleCat.of R₁ R₁) ≫
        (objSelfIso (f₂₃.comp f₁₂)).hom =
      (ModuleCat.extendScalars f₂₃).map (objSelfIso f₁₂).hom ≫ (objSelfIso f₂₃).hom := by
  rw [← objSelfIso_extendScalarsComp f₁₂ f₂₃, ← Category.assoc, Iso.inv_hom_id_app,
    Category.id_comp]

/-- The contraction `R₃ ⊗_{R₂} (R₂ ⊗_{R₁} −) ≅ R₃ ⊗_{R₁} −`, read at the base ring `R₁` and
followed by the identification of `R₃ ⊗_{R₁} R₁` with `R₃`, contracts the two tensor factors in
turn.  The renaming of extension of scalars along an equality of ring maps is invisible to
`ModuleCat.ExtendScalars.objSelfIso`, so this is
`ModuleCat.ExtendScalars.objSelfIso_extendScalarsComp_inv`. -/
theorem objSelfIso_extendScalarsCompIso (f₁₂ : R₁ →+* R₂) (f₂₃ : R₂ →+* R₃) {f : R₁ →+* R₃}
    (hf : f₂₃.comp f₁₂ = f)
    (e : ModuleCat.extendScalars.{u, u, u} (f₂₃.comp f₁₂) = ModuleCat.extendScalars.{u, u, u} f) :
    ((ModuleCat.extendScalarsComp f₁₂ f₂₃).symm ≪≫ eqToIso e).hom.app (ModuleCat.of R₁ R₁) ≫
        (objSelfIso f).hom =
      (ModuleCat.extendScalars f₂₃).map (objSelfIso f₁₂).hom ≫ (objSelfIso f₂₃).hom := by
  subst hf
  rw [Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app, Category.assoc, eqToHom_refl,
    Category.id_comp, Iso.symm_hom, objSelfIso_extendScalarsComp_inv]

end ModuleCat.ExtendScalars

/-! ### The comparison `f^*𝒪 ⟶ 𝒪'` as an inverse isomorphism -/

namespace AlgebraicGeometry.RingedToposHom

universe v₁ u₁ w₁ v₂ u₂ w₂

variable {X : RingedTopos.{v₁, u₁, w₁}} {Y : RingedTopos.{v₂, u₂, w₂}}
  [X.J.HasSheafCompose (forget RingCat.{w₁})] [Y.J.HasSheafCompose (forget RingCat.{w₂})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w₂} RingCat.{w₂})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w₁})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w₂})]
  [HasWeakSheafify X.J AddCommGrpCat.{w₁}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w₁}]

/-- **The comparison `f^*𝒪 ⟶ 𝒪'` of Stacks 03LU is the inverse of the isomorphism built by
corepresentability.**  It is a retraction of it
(`AlgebraicGeometry.RingedToposHom.pullbackModulesObjUnitIso_hom_comp_pullbackUnitStructureMap`),
and a retraction of an isomorphism is its inverse. -/
theorem pullbackModulesObjUnitIso_inv (f : RingedToposHom X Y) :
    (Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso f.toModulesHom).inv =
      f.pullbackUnitStructureMap :=
  calc (Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso f.toModulesHom).inv
      = (Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso f.toModulesHom).inv ≫
          (Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso f.toModulesHom).hom ≫
            f.pullbackUnitStructureMap := by
        rw [pullbackModulesObjUnitIso_hom_comp_pullbackUnitStructureMap, Category.comp_id]
    _ = f.pullbackUnitStructureMap := by rw [Iso.inv_hom_id_assoc]

end AlgebraicGeometry.RingedToposHom

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The comparison `f^*𝒪 ⟶ 𝒪'` of a composite -/

section Spaces

variable {X Y Z : AlgebraicSpaces B S hS}

/-- **The comparison `f^*𝒪 ⟶ 𝒪'` of Stacks 03LU is compatible with composition**, across the
contraction `AlgebraicGeometry.Space.smallEtaleToposPullbackCompIso` of the inverse images of
modules of the small étale ringed topoi.

The contraction is the comparison of the inverse image of a composite of morphisms of ringed
topoi with the composite of the inverse images, followed by the inverse-image comparison of the
2-isomorphism identifying the composite of the two morphisms of ringed topoi with the morphism of
ringed topoi of the composite; so this is
`AlgebraicGeometry.RingedToposHom.pullbackModulesCompIso_hom_app_comp_pullbackUnitStructureMap`
followed by its 2-isomorphism invariance
`AlgebraicGeometry.RingedToposHom.TwoIso.pullbackModulesIso_hom_app_comp_pullbackUnitStructureMap`
of the file `InverseImageIdealSheafToposTwoIso`. -/
theorem smallEtaleToposPullbackCompIso_inv_app_unit_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    (smallEtaleToposPullbackCompIso f g).inv.app
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedTopos B S hS Z).O)) ≫
        (smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules.map
          (smallEtaleRingedToposHom B S hS g).pullbackUnitStructureMap ≫
        (smallEtaleRingedToposHom B S hS f).pullbackUnitStructureMap =
      (smallEtaleRingedToposHom B S hS (f ≫ g)).pullbackUnitStructureMap := by
  have hcomp : ((smallEtaleRingedToposHom B S hS f).pullbackModulesCompIso
          (smallEtaleRingedToposHom B S hS g)).hom.app
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedTopos B S hS Z).O)) ≫
        (smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules.map
          (smallEtaleRingedToposHom B S hS g).pullbackUnitStructureMap ≫
        (smallEtaleRingedToposHom B S hS f).pullbackUnitStructureMap =
      ((smallEtaleRingedToposHom B S hS g).comp
        (smallEtaleRingedToposHom B S hS f)).pullbackUnitStructureMap :=
    AlgebraicGeometry.RingedToposHom.pullbackModulesCompIso_hom_app_comp_pullbackUnitStructureMap
      (smallEtaleRingedToposHom B S hS g) (smallEtaleRingedToposHom B S hS f)
  have htwo : (smallEtaleRingedToposHom_compTwoIso B S hS f g).pullbackModulesIso.hom.app
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedTopos B S hS Z).O)) ≫
        (smallEtaleRingedToposHom B S hS (f ≫ g)).pullbackUnitStructureMap =
      ((smallEtaleRingedToposHom B S hS g).comp
        (smallEtaleRingedToposHom B S hS f)).pullbackUnitStructureMap :=
    AlgebraicGeometry.RingedToposHom.TwoIso.pullbackModulesIso_hom_app_comp_pullbackUnitStructureMap
      (smallEtaleRingedToposHom_compTwoIso B S hS f g)
  simp only [smallEtaleToposPullbackCompIso, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Category.assoc]
  rw [hcomp, ← htwo, Iso.inv_hom_id_app_assoc]

/-- `AlgebraicGeometry.Space.smallEtaleToposPullbackCompIso_inv_app_unit_comp` across the
renaming of the inverse image along an equality of morphisms of algebraic spaces. -/
theorem smallEtaleToposPullbackCompIso_eqToIso_inv_app_unit_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    {k : X ⟶ Z} (hk : f ≫ g = k) :
    (smallEtaleToposPullbackCompIso f g ≪≫ eqToIso (congrArg
            (fun m => (smallEtaleRingedToposHom B S hS m).toModulesHom.pullbackModules)
            hk)).inv.app
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedTopos B S hS Z).O)) ≫
        (smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules.map
          (smallEtaleRingedToposHom B S hS g).pullbackUnitStructureMap ≫
        (smallEtaleRingedToposHom B S hS f).pullbackUnitStructureMap =
      (smallEtaleRingedToposHom B S hS k).pullbackUnitStructureMap := by
  subst hk
  exact Stacks.CategoryTheory.BaseChange.trans_eqToIso_refl_inv_app_comp _ _ _
    (smallEtaleToposPullbackCompIso_inv_app_unit_comp B S hS f g)

end Spaces

/-! ### The contraction of the inverse images along represented morphisms -/

section Represented

variable {U'' U' U : BigFppfOver B S hS} (h : U'' ⟶ U') (g : U' ⟶ U)

/-- **The contraction `g^* ⋙ h^* ≅ (h ≫ g)^*`** of the inverse images of modules along
represented morphisms of algebraic spaces: the contraction
`AlgebraicGeometry.Space.smallEtaleToposPullbackCompIso`, followed by the renaming of the inverse
image along `AlgebraicGeometry.Space.representedSpaceMap_comp`. -/
def representedSpacePullbackCompIso :
    (smallEtaleRingedToposHom B S hS
          (representedSpaceMap B S hS g)).toModulesHom.pullbackModules ⋙
        (smallEtaleRingedToposHom B S hS
          (representedSpaceMap B S hS h)).toModulesHom.pullbackModules ≅
      (smallEtaleRingedToposHom B S hS
        (representedSpaceMap B S hS (h ≫ g))).toModulesHom.pullbackModules :=
  smallEtaleToposPullbackCompIso (representedSpaceMap B S hS h)
      (representedSpaceMap B S hS g) ≪≫
    eqToIso (congrArg
      (fun m => (smallEtaleRingedToposHom B S hS m).toModulesHom.pullbackModules)
      (representedSpaceMap_comp B S hS h g))

/-- **The comparison `f^*𝒪 ⟶ 𝒪'` of Stacks 03LU is compatible with composition of represented
morphisms**, across `AlgebraicGeometry.Space.representedSpacePullbackCompIso`.  This is
`AlgebraicGeometry.Space.smallEtaleToposPullbackCompIso_eqToIso_inv_app_unit_comp` at the
equality `AlgebraicGeometry.Space.representedSpaceMap_comp`. -/
theorem representedSpacePullbackCompIso_inv_app_unit_comp :
    (representedSpacePullbackCompIso B S hS h g).inv.app
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedTopos B S hS
              ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O)) ≫
        (smallEtaleRingedToposHom B S hS
            (representedSpaceMap B S hS h)).toModulesHom.pullbackModules.map
          (smallEtaleRingedToposHom B S hS
            (representedSpaceMap B S hS g)).pullbackUnitStructureMap ≫
        (smallEtaleRingedToposHom B S hS
          (representedSpaceMap B S hS h)).pullbackUnitStructureMap =
      (smallEtaleRingedToposHom B S hS
        (representedSpaceMap B S hS (h ≫ g))).pullbackUnitStructureMap :=
  smallEtaleToposPullbackCompIso_eqToIso_inv_app_unit_comp B S hS _ _
    (representedSpaceMap_comp B S hS h g)

/-- **The map of rings of global functions of a composite is the composite of the maps.**  The
underlying scheme of a composite is the composite of the underlying schemes, and global sections
of a composite is the composite of global sections. -/
theorem representedAffineCommRingCatHom_comp :
    representedAffineCommRingCatHom B S hS (h ≫ g) =
      representedAffineCommRingCatHom B S hS g ≫ representedAffineCommRingCatHom B S hS h :=
  (congrArg Scheme.Hom.appTop ((BigFppfOver.toScheme B S hS).map_comp h g)).trans
    (Scheme.Hom.comp_appTop _ _)

/-- `AlgebraicGeometry.Space.representedAffineCommRingCatHom_comp`, read on the underlying ring
homomorphisms. -/
theorem representedAffineCommRingCatHom_comp_hom :
    (representedAffineCommRingCatHom B S hS (h ≫ g)).hom =
      (representedAffineCommRingCatHom B S hS h).hom.comp
        (representedAffineCommRingCatHom B S hS g).hom :=
  (congrArg CommRingCat.Hom.hom (representedAffineCommRingCatHom_comp B S hS h g)).trans
    (CommRingCat.hom_comp _ _)

/-- **The contraction `R'' ⊗_{R'} (R' ⊗_R −) ≅ R'' ⊗_R −`** of extension of scalars along the
maps of rings of global functions: `ModuleCat.extendScalarsComp`, followed by the renaming of
extension of scalars along `AlgebraicGeometry.Space.representedAffineCommRingCatHom_comp_hom`. -/
def representedAffineExtendScalarsCompIso :
    ModuleCat.extendScalars (representedAffineCommRingCatHom B S hS g).hom ⋙
        ModuleCat.extendScalars (representedAffineCommRingCatHom B S hS h).hom ≅
      ModuleCat.extendScalars (representedAffineCommRingCatHom B S hS (h ≫ g)).hom :=
  (ModuleCat.extendScalarsComp (representedAffineCommRingCatHom B S hS g).hom
      (representedAffineCommRingCatHom B S hS h).hom).symm ≪≫
    eqToIso (congrArg ModuleCat.extendScalars.{u, u, u}
      (representedAffineCommRingCatHom_comp_hom B S hS h g).symm)

/-- At the base ring, the contraction
`AlgebraicGeometry.Space.representedAffineExtendScalarsCompIso` followed by the identification of
`R'' ⊗_R R` with `R''` contracts the two tensor factors in turn.  This is
`ModuleCat.ExtendScalars.objSelfIso_extendScalarsCompIso`. -/
theorem representedAffineExtendScalarsCompIso_hom_app_self :
    (representedAffineExtendScalarsCompIso B S hS h g).hom.app
          (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
            Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ≫
        (ModuleCat.ExtendScalars.objSelfIso
          (representedAffineCommRingCatHom B S hS (h ≫ g)).hom).hom =
      (ModuleCat.extendScalars (representedAffineCommRingCatHom B S hS h).hom).map
          (ModuleCat.ExtendScalars.objSelfIso
            (representedAffineCommRingCatHom B S hS g).hom).hom ≫
        (ModuleCat.ExtendScalars.objSelfIso
          (representedAffineCommRingCatHom B S hS h).hom).hom :=
  ModuleCat.ExtendScalars.objSelfIso_extendScalarsCompIso _ _
    (representedAffineCommRingCatHom_comp_hom B S hS h g).symm _

end Represented

/-! ### The composition coherence -/

section Affine

variable {U'' U' U : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U'')]
  (h : U'' ⟶ U') (g : U' ⟶ U)

/-- The identification `AlgebraicGeometry.Space.representedAffineAssociatedObjUnitIso` of the
associated module of the ring of global functions with the structure sheaf, retyped with the
structure sheaf written as the unit of the small étale ringed topos.  See the implementation
notes: this retyping is where the two spellings of the structure sheaf are identified. -/
def representedAffineAssociatedObjUnitIso' (V : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] :
    (representedAffineAssociated B S hS V).obj
        (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos B S hS
          ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩).O) :=
  representedAffineAssociatedObjUnitIso B S hS V

/-- The trivialization `AlgebraicGeometry.Space.representedAffinePullbackUnitIso` of `g^*(R^~)`,
read through the comparison `g^*𝒪 ⟶ 𝒪'` of Stacks 03LU
(`AlgebraicGeometry.RingedToposHom.pullbackModulesObjUnitIso_inv`). -/
theorem representedAffinePullbackUnitIso_hom :
    (representedAffinePullbackUnitIso B S hS g).hom =
      (smallEtaleRingedToposHom B S hS
            (representedSpaceMap B S hS g)).toModulesHom.pullbackModules.map
          (representedAffineAssociatedObjUnitIso' B S hS U).hom ≫
        (smallEtaleRingedToposHom B S hS
            (representedSpaceMap B S hS g)).pullbackUnitStructureMap ≫
          (representedAffineAssociatedObjUnitIso' B S hS U').inv :=
  congrArg (fun x => (smallEtaleRingedToposHom B S hS
          (representedSpaceMap B S hS g)).toModulesHom.pullbackModules.map
        (representedAffineAssociatedObjUnitIso' B S hS U).hom ≫ x ≫
      (representedAffineAssociatedObjUnitIso' B S hS U').inv)
    (AlgebraicGeometry.RingedToposHom.pullbackModulesObjUnitIso_inv
      (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g)))

/-- **The trivialization of `f^*(R^~)` is compatible with composition.**  This is the composition
coherence of the underived base change isomorphism at `M = R`: the associated modules of the
rings cancel in the middle, the comparison `f^*𝒪 ⟶ 𝒪'` of Stacks 03LU passes through the
contraction of the inverse images by
`AlgebraicGeometry.Space.representedSpacePullbackCompIso_inv_app_unit_comp`, and the remaining
associated module of the ring is carried through the contraction by its naturality. -/
theorem representedAffinePullbackUnitIso_comp :
    (representedSpacePullbackCompIso B S hS h g).inv.app
          ((representedAffineAssociated B S hS U).obj
            (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
              Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))) ≫
        (smallEtaleRingedToposHom B S hS
            (representedSpaceMap B S hS h)).toModulesHom.pullbackModules.map
          (representedAffinePullbackUnitIso B S hS g).hom ≫
        (representedAffinePullbackUnitIso B S hS h).hom =
      (representedAffinePullbackUnitIso B S hS (h ≫ g)).hom :=
  Stacks.CategoryTheory.BaseChange.contraction_inv_app_comp_trivialization
    (representedSpacePullbackCompIso B S hS h g)
    (representedAffineAssociatedObjUnitIso' B S hS U)
    (representedAffineAssociatedObjUnitIso' B S hS U')
    (representedAffineAssociatedObjUnitIso' B S hS U'')
    (representedSpacePullbackCompIso_inv_app_unit_comp B S hS h g)
    (representedAffinePullbackUnitIso_hom B S hS g)
    (representedAffinePullbackUnitIso_hom B S hS h)
    (representedAffinePullbackUnitIso_hom B S hS (h ≫ g))

/-- **The pasted isomorphism** `Φ_R ⋙ (h ≫ g)^* ≅ (R'' ⊗_R −) ⋙ Φ_{R''}`: the contraction of the
inverse images, the base change isomorphism of `g` pulled back along `h`, the base change
isomorphism of `h`, and the contraction of the extensions of scalars. -/
def representedAffineAssociatedPullbackCompIso :
    representedAffineAssociated B S hS U ⋙
        (smallEtaleRingedToposHom B S hS
          (representedSpaceMap B S hS (h ≫ g))).toModulesHom.pullbackModules ≅
      ModuleCat.extendScalars (representedAffineCommRingCatHom B S hS (h ≫ g)).hom ⋙
        representedAffineAssociated B S hS U'' :=
  Stacks.CategoryTheory.BaseChange.pastedBaseChangeIso
    (representedSpacePullbackCompIso B S hS h g)
    (representedAffineExtendScalarsCompIso B S hS h g)
    (representedAffineAssociatedPullbackIso B S hS g)
    (representedAffineAssociatedPullbackIso B S hS h)

/-- **The underived affine base change isomorphism is compatible with composition.**  Pasting the
isomorphism `g^*(M^~) ≅ (R' ⊗_R M)^~` of `g` with the isomorphism `h^*(N^~) ≅ (R'' ⊗_{R'} N)^~`
of `h`, and contracting `g^* ⋙ h^*` to `(h ≫ g)^*` and `R'' ⊗_{R'} (R' ⊗_R −)` to `R'' ⊗_R −`,
gives the isomorphism of `h ≫ g`.

Both sides are isomorphisms `Φ_R ⋙ (h ≫ g)^* ≅ (R'' ⊗_R −) ⋙ Φ_{R''}`, so this is
`AlgebraicGeometry.Space.representedAffineAssociatedPullbackIso_eq_of_hom_app_self` applied to
the value of the pasted isomorphism at `M = R`, which is the composition coherence of the
trivializations `AlgebraicGeometry.Space.representedAffinePullbackUnitIso_comp`. -/
theorem representedAffineAssociatedPullbackIso_comp :
    representedAffineAssociatedPullbackCompIso B S hS h g =
      representedAffineAssociatedPullbackIso B S hS (h ≫ g) :=
  representedAffineAssociatedPullbackIso_eq_of_hom_app_self B S hS (h ≫ g) _
    (Stacks.CategoryTheory.BaseChange.pastedBaseChangeIso_hom_app_self _ _ _ _
      (representedAffineExtendScalarsCompIso_hom_app_self B S hS h g)
      (representedAffineAssociatedPullbackIso_hom_app_self B S hS g)
      (representedAffineAssociatedPullbackIso_hom_app_self B S hS h)
      (representedAffinePullbackUnitIso_comp B S hS h g))

end Affine

end AlgebraicGeometry.Space

end
