module

public import StacksFrontier.CategoryTheory.Abelian.ExtMapFunctorial
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ConstantSheafInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.OpenClosedSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.Exactness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PushforwardBaseChange
public import StacksFrontier.Topology.Sheaves.Cohomology.CechOfPresheavesOfModules.DegreeOneVanishingGluesSections

/-!
# Restricting a boundary class of étale cohomology to an étale scheme

Let `X` be a scheme, `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` a short exact sequence of abelian sheaves on
`X_étale` and `c` a global section of `F₃`. Its boundary `∂c ∈ H¹(X, F₁)` restricts to zero on an
étale `X`-scheme `V` exactly when `c|_V` lifts to a section of `F₂` over `V`. This file proves
both directions, with restriction read through the two spellings of the inverse image along an
étale morphism, and records how the vanishing of a class under inverse image behaves along
composites and along isomorphisms of exact functors.

## Main results

* `Stacks.ExtFunctorial.mapExactFunctor_eq_zero_iff_of_iso` — isomorphic exact functors kill the
  same `Ext` classes.
* `Stacks.EtaleCohomology.mapExactFunctor_etaleAbelianInverseImage_comp_eq_zero_iff` — a class
  dies under the inverse image along `b ≫ a` exactly when its inverse image along `a` dies under
  the inverse image along `b`.
* `Stacks.EtaleCohomology.mapExactFunctor_etaleAbelianInverseImage_eq_zero_of_lift` — if `c|_V`
  lifts, `∂c` dies under the inverse image along `V ⟶ X`.
* `Stacks.EtaleCohomology.exists_lift_of_mapExactFunctor_etaleRestriction_eq_zero` — if `∂c`
  dies under restriction to `V`, then `c|_V` lifts.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite AlgebraicGeometry

universe w w' u

namespace Stacks.ExtFunctorial

variable {C : Type*} [Category* C] [Abelian C] {D : Type*} [Category* D] [Abelian D]

/-- **Isomorphic exact functors kill the same `Ext` classes.** -/
theorem mapExactFunctor_eq_zero_iff_of_iso [HasExt.{w} C] [HasExt.{w'} D] [EnoughInjectives C]
    {L L' : C ⥤ D} [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [L'.Additive] [PreservesFiniteLimits L'] [PreservesFiniteColimits L'] (τ : L ≅ L')
    {X Y : C} {n : ℕ} (x : Ext.{w} X Y n) :
    x.mapExactFunctor L = 0 ↔ x.mapExactFunctor L' = 0 := by
  have key : ∀ {L L' : C ⥤ D} [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
      [L'.Additive] [PreservesFiniteLimits L'] [PreservesFiniteColimits L'] (τ : L ≅ L'),
      x.mapExactFunctor L = 0 → x.mapExactFunctor L' = 0 := fun τ h0 => by
    have h := mk₀_comp_mapExactFunctor τ.hom X n x
    rw [h0, Ext.zero_comp] at h
    simpa [Ext.mk₀_comp_mk₀_assoc] using
      congrArg (fun y => (Ext.mk₀ (τ.inv.app X)).comp y (zero_add n)) h
  exact ⟨key τ, key τ.symm⟩

end Stacks.ExtFunctorial

namespace Stacks.EtaleCohomology

attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse
  comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {X Y Z : Scheme.{u}}

/-- **Vanishing under inverse image along a composite.** A class dies under the inverse image
along `b ≫ a` exactly when its inverse image along `a` dies under the inverse image along
`b`. -/
theorem mapExactFunctor_etaleAbelianInverseImage_comp_eq_zero_iff (a : Y ⟶ X) (b : Z ⟶ Y)
    {A B : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} {n : ℕ} (x : Ext.{u + 1} A B n) :
    (x.mapExactFunctor (etaleAbelianInverseImage.{u, 0} a)).mapExactFunctor
        (etaleAbelianInverseImage.{u, 0} b) = 0 ↔
      x.mapExactFunctor (etaleAbelianInverseImage.{u, 0} (b ≫ a)) = 0 := by
  rw [Stacks.ExtFunctorial.mapExactFunctor_comp_functor]
  exact Stacks.ExtFunctorial.mapExactFunctor_eq_zero_iff_of_iso
    (etaleAbelianInverseImageCompIso'.{u, 0} b a (b ≫ a) rfl).symm x

/-- **Restriction along an étale morphism, in its two spellings, kills the same classes.** -/
theorem mapExactFunctor_etaleAbelianInverseImage_eq_zero_iff_etaleRestriction (j : Y ⟶ X)
    [Etale j] {A B : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} {n : ℕ}
    (x : Ext.{u + 1} A B n) :
    x.mapExactFunctor (etaleAbelianInverseImage.{u, 0} j) = 0 ↔
      x.mapExactFunctor (etaleRestriction.{u, 0} j) = 0 :=
  Stacks.ExtFunctorial.mapExactFunctor_eq_zero_iff_of_iso
    (etaleAbelianInverseImageRestrictionIso.{u, 0} j) x

/-- **Restriction of a class which dies on a composite.** If `x` dies under the inverse image
along `b ≫ a`, then its restriction along `a` dies under the inverse image along `b`. -/
theorem mapExactFunctor_etaleCohomologyRestrictionMap_eq_zero (a : Y ⟶ X) (b : Z ⟶ Y)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) {q : ℕ} (x : Sheaf.H.{u + 1} F q)
    (h : x.mapExactFunctor (etaleAbelianInverseImage.{u, 0} (b ≫ a)) = 0) :
    (etaleCohomologyRestrictionMap.{u, 0, u + 1} a F q x).mapExactFunctor
      (etaleAbelianInverseImage.{u, 0} b) = 0 := by
  rw [etaleCohomologyRestrictionMap_apply.{u, 0, u + 1}, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀, (mapExactFunctor_etaleAbelianInverseImage_comp_eq_zero_iff a b x).2 h,
    Ext.comp_zero]

section Boundary

open Scheme.Etale

variable {S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})} (hS : S.ShortExact)
  (c : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ S.X₃)

include hS in
/-- **A boundary class whose restriction to `V` vanishes comes from a section that lifts over
`V`.** Let `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` be short exact on `X_étale` and `c : ℤ ⟶ F₃`. If the boundary
`∂c ∈ H¹(X, F₁)` dies under restriction to the étale `X`-scheme `V`, then the restriction to `V`
of the global section `c(1)` of `F₃` lifts to a section of `F₂` over `V`. -/
theorem exists_lift_of_mapExactFunctor_etaleRestriction_eq_zero (V : X.Etale)
    (h : ((Ext.mk₀ c).comp hS.extClass (zero_add 1)).mapExactFunctor
      (etaleRestriction.{u, 0} V.hom) = 0) :
    ∃ s : S.X₂.obj.obj (op V), S.g.hom.app (op V) s =
      S.X₃.obj.map ((etaleSiteTerminalIsTerminal X).from V).op
        (c.hom.app (op (etaleSiteTerminal X))
          (Stacks.ConstantSheaf.constantSheafSection X.smallEtaleTopology _
            (AddCommGrpCat.of (ULift.{u + 1} ℤ)) (etaleSiteTerminal X) (ULift.up 1))) := by
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.mapExactFunctor_extClass] at h
  obtain ⟨x₂, hx₂⟩ := Ext.covariant_sequence_exact₃ _
    (hS.map_of_exact (etaleRestriction.{u, 0} V.hom)) _ (zero_add 1) h
  obtain ⟨l, rfl⟩ := (Ext.mk₀_bijective _ _).2 x₂
  rw [Ext.mk₀_comp_mk₀] at hx₂
  have hl : l ≫ (etaleRestriction.{u, 0} V.hom).map S.g =
      (etaleRestriction.{u, 0} V.hom).map c := (Ext.mk₀_bijective _ _).1 hx₂
  let TV := etaleSiteTerminal V.left
  let E := (smallEtaleCompose V.hom).obj TV
  let gen := Stacks.ConstantSheaf.constantSheafSection X.smallEtaleTopology _
    (AddCommGrpCat.of (ULift.{u + 1} ℤ)) (etaleSiteTerminal X) (ULift.up 1)
  let e := ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))).obj.map ((etaleSiteTerminalIsTerminal X).from E).op gen
  have hs' : S.g.hom.app (op E) (l.hom.app (op TV) e) =
      S.X₃.obj.map ((etaleSiteTerminalIsTerminal X).from E).op
        (c.hom.app (op (etaleSiteTerminal X)) gen) := by
    have h1 := congrArg (fun φ => φ.hom.app (op TV) e) hl
    change S.g.hom.app (op E) (l.hom.app (op TV) e) = c.hom.app (op E) e at h1
    rw [h1]
    exact NatTrans.naturality_apply c.hom _ gen
  let i : V ⟶ E := MorphismProperty.Over.homMk (𝟙 V.left) <| by
    change 𝟙 V.left ≫ (𝟙 V.left ≫ V.hom) = V.hom
    simp
  refine ⟨S.X₂.obj.map i.op (l.hom.app (op TV) e), ?_⟩
  refine (NatTrans.naturality_apply S.g.hom i.op (l.hom.app (op TV) e)).trans ?_
  rw [hs', ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
    (etaleSiteTerminalIsTerminal X).hom_ext (i ≫ _) ((etaleSiteTerminalIsTerminal X).from V)]

include hS in
/-- **A boundary class dies on an étale scheme over which its section lifts.** Let
`0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` be short exact on `X_étale` and `c : ℤ ⟶ F₃`. If the restriction to the
étale `X`-scheme `V` of the global section `c(1)` of `F₃` lifts to a section of `F₂` over `V`,
then the boundary `∂c ∈ H¹(X, F₁)` dies under the inverse image along `V ⟶ X`.

The inverse image `j⁻¹` is left adjoint to the direct image `j_*` along `j : V ⟶ X`, whose
sections over `U` are those over `U ×_X V`; the transpose of the lift, restricted along the
diagonal of `V ×_X V`, is a section over the final object `X ×_X V` lifting the image of `c(1)`
under the unit, and it transposes back to a factorization of `j⁻¹c` through `j⁻¹F₂ ⟶ j⁻¹F₃`. -/
theorem mapExactFunctor_etaleAbelianInverseImage_eq_zero_of_lift (V : X.Etale)
    (s : S.X₂.obj.obj (op V))
    (hs : S.g.hom.app (op V) s =
      S.X₃.obj.map ((etaleSiteTerminalIsTerminal X).from V).op
        (c.hom.app (op (etaleSiteTerminal X))
          (Stacks.ConstantSheaf.constantSheafSection X.smallEtaleTopology _
            (AddCommGrpCat.of (ULift.{u + 1} ℤ)) (etaleSiteTerminal X) (ULift.up 1)))) :
    ((Ext.mk₀ c).comp hS.extClass (zero_add 1)).mapExactFunctor
      (etaleAbelianInverseImage.{u, 0} V.hom) = 0 := by
  let L := etaleAbelianInverseImage.{u, 0} V.hom
  let adj := etaleAbelianInverseImageDirectImageAdj.{u, 0} V.hom
  let bc := smallEtaleBaseChange V.hom
  let T := etaleSiteTerminal X
  let gen := Stacks.ConstantSheaf.constantSheafSection X.smallEtaleTopology _
    (AddCommGrpCat.of (ULift.{u + 1} ℤ)) T (ULift.up 1)
  let d : bc.obj T ⟶ bc.obj V := smallEtaleFactorizationHom V.hom (bc.obj T).hom rfl
  let m : (L.obj S.X₂).obj.obj (op (bc.obj T)) :=
    (L.obj S.X₂).obj.map d.op ((adj.unit.app S.X₂).hom.app (op V) s)
  have hm : (L.map S.g).hom.app (op (bc.obj T)) m =
      (adj.unit.app S.X₃).hom.app (op T) (c.hom.app (op T) gen) := by
    have h1 := NatTrans.naturality_apply (L.map S.g).hom d.op
      ((adj.unit.app S.X₂).hom.app (op V) s)
    have h2 := congrArg (fun φ => φ.hom.app (op V) s) (adj.unit.naturality S.g)
    change (adj.unit.app S.X₃).hom.app (op V) (S.g.hom.app (op V) s) =
      (L.map S.g).hom.app (op (bc.obj V)) ((adj.unit.app S.X₂).hom.app (op V) s) at h2
    have h3 := NatTrans.naturality_apply (adj.unit.app S.X₃).hom
      ((etaleSiteTerminalIsTerminal X).from V).op (c.hom.app (op T) gen)
    change (adj.unit.app S.X₃).hom.app (op V) (S.X₃.obj.map _ (c.hom.app (op T) gen)) =
      (L.obj S.X₃).obj.map (bc.map ((etaleSiteTerminalIsTerminal X).from V)).op
        ((adj.unit.app S.X₃).hom.app (op T) (c.hom.app (op T) gen)) at h3
    refine h1.trans ?_
    rw [← h2, hs, h3]
    change ((L.obj S.X₃).obj.map (bc.map ((etaleSiteTerminalIsTerminal X).from V)).op ≫
      (L.obj S.X₃).obj.map d.op) _ = _
    rw [← Functor.map_comp, ← op_comp,
      ((etaleSiteTerminalIsTerminal X).isTerminalObj bc).hom_ext (d ≫ _) (𝟙 _), op_id]
    exact ConcreteCategory.congr_hom ((L.obj S.X₃).obj.map_id _) _
  let φ : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ (etaleAbelianDirectImage.{u, 0} V.hom).obj
        (L.obj S.X₂) :=
    ((constantSheafAdj _ _ (etaleSiteTerminalIsTerminal X)).homEquiv _ _).symm
      (Stacks.Cohomology.CechDegreeOneVanishing.genHom _ m)
  have hl : (adj.homEquiv _ _).symm φ ≫ L.map S.g = L.map c := by
    apply (adj.homEquiv _ _).injective
    rw [adj.homEquiv_naturality_right, Equiv.apply_symm_apply, adj.homEquiv_unit,
      show adj.unit.app _ ≫ (etaleAbelianDirectImage.{u, 0} V.hom).map (L.map c) =
        c ≫ adj.unit.app S.X₃ from (adj.unit.naturality c).symm]
    apply ((constantSheafAdj _ _ (etaleSiteTerminalIsTerminal X)).homEquiv _ _).injective
    have hφ : (Stacks.ConstantSheaf.constantSheafSection X.smallEtaleTopology _
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) T ≫ φ.hom.app (op T)) (ULift.up 1) = m := by
      rw [← Stacks.ConstantSheaf.constantSheafAdj_homEquiv_apply_eq, Equiv.apply_symm_apply]
      exact Stacks.Cohomology.CechDegreeOneVanishing.genHom_apply _ m
    rw [Stacks.ConstantSheaf.constantSheafAdj_homEquiv_apply_eq,
      Stacks.ConstantSheaf.constantSheafAdj_homEquiv_apply_eq]
    ext ⟨n⟩
    have hn : (ULift.up n : ULift.{u + 1} ℤ) = n • ULift.up 1 := by
      ext
      simp
    rw [hn, map_zsmul, map_zsmul]
    congr 1
    change (L.map S.g).hom.app (op (bc.obj T))
      ((Stacks.ConstantSheaf.constantSheafSection X.smallEtaleTopology _
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) T ≫ φ.hom.app (op T)) (ULift.up 1)) = _
    rw [hφ, hm]
    rfl
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.mapExactFunctor_extClass, ← hl,
    ← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero,
    show (Ext.mk₀ (L.map S.g)).comp (hS.map_of_exact L).extClass (zero_add 1) = 0 from
      (hS.map_of_exact L).comp_extClass, Ext.comp_zero]

end Boundary

end Stacks.EtaleCohomology

end
