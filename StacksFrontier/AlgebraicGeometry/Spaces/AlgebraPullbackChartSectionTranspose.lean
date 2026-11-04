module

public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraPullbackChartSection

/-!
# The chart section of a pulled-back algebra, at the module and at the ring level

Let `g : Y ⟶ X` be a morphism of algebraic spaces and `A` a sheaf of `𝒪_X`-algebras on the small
étale site of `X`.  The module underlying the pullback algebra `g^* A` is identified with the
pullback `g^*(A_mod)` of the module underlying `A` by
`AlgebraicGeometry.Space.underlyingModuleAlgebraPullbackModulePullbackIso`.  This file shows that
the identification carries the chart section of the pullback of modules attached to a section
`s` of `A` over the chart of a chart diagram to the chart projection of the transpose, along the
inverse-image/direct-image adjunction of sheaves of commutative rings, of the first inclusion
`g⁻¹ A ⟶ g^* A` of the pushout.

## Main results

* `AlgebraicGeometry.Space.underlyingModuleAlgebraPullbackModulePullbackIso_chartSection`.

## Implementation notes

Every step is an identification that holds on the nose, but some of them are very expensive for
the elaborator: the inverse image of a sheaf of modules computed through Stacks 03D7 and the
one computed through the interchange of inverse image and restriction of scalars are spelled
differently, as are the underlying sheaves of sets of an inverse image of rings and the inverse
image of the underlying sheaves of sets.  The proofs therefore never compare two such spellings
inside one morphism statement.  They go through heterogeneous equalities and through statements
generic in the target algebra, so that each declaration performs at most one such
identification, on objects.

## References

* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward Stacks.Sheaves.RingedToposModules

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS}

/-- The source of a morphism, as a function of the morphism. -/
abbrev homSource {C : Type*} [Category C] {P Q : C} (_ : P ⟶ Q) : C := P

/-- The inverse image of the module underlying `A` is the source of the interchange of inverse
image and restriction of scalars at the free module of rank one over `A`. -/
theorem inverseImageModules_obj_underlyingModule_eq_domOf (g : Y ⟶ X)
    (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) :
    (inverseImageModules (smallEtaleRingedToposHom B S hS g).toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf (structureSheaf B S hS X.1 X.2))).obj
            A.underlyingModule =
      homSource (pullbackModuleObjRestrictScalarsIso
          (SmallEtale.topology B S hS Y.1)
          ((smallEtaleRingedToposHom B S hS g).toToposHom).inverseImage
          (Stacks.FlatChangeOfRings.ringSheafMap
            (O₁ := structureSheaf B S hS X.1 X.2) (O₂ := A.right) A.hom)
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf A.right))).symm.hom :=
  rfl

/-- Transposes along an adjunction of heterogeneously equal morphisms between equal objects are
heterogeneously equal. -/
theorem _root_.CategoryTheory.Adjunction.homEquiv_heq_of_eq {C D : Type*} [Category C]
    [Category D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {A₁ A₂ : C} {B₁ B₂ : D}
    (hA : A₁ = A₂) (hB : B₁ = B₂) {k₁ : F.obj A₁ ⟶ B₁} {k₂ : F.obj A₂ ⟶ B₂} (hk : HEq k₁ k₂) :
    HEq (adj.homEquiv A₁ B₁ k₁) (adj.homEquiv A₂ B₂ k₂) := by
  subst hA hB
  cases hk
  rfl

/-- The forward map of the identification of `g^*(A_mod)` with the module underlying `g^*A`,
unfolded into its three factors. -/
theorem underlyingModuleAlgebraPullbackModulePullbackIso_hom_heq (g : Y ⟶ X)
    (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) :
    HEq (underlyingModuleAlgebraPullbackModulePullbackIso B S hS g A).hom
      (((Stacks.FlatChangeOfRings.extendScalars (structurePullbackMap B S hS g)).mapIso
            (pullbackModuleObjRestrictScalarsIso
          (SmallEtale.topology B S hS Y.1)
          ((smallEtaleRingedToposHom B S hS g).toToposHom).inverseImage
          (Stacks.FlatChangeOfRings.ringSheafMap
            (O₁ := structureSheaf B S hS X.1 X.2) (O₂ := A.right) A.hom)
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf A.right))).symm ≪≫
          eqToIso (congrArg (Stacks.FlatChangeOfRings.extendScalars
            (structurePullbackMap B S hS g)).obj
              (underlyingModule_inverseImageAlgebra B S hS g A).symm) ≪≫
          (underlyingModuleAlgebraPullbackIso B S hS g A).symm).hom) :=
  HEq.rfl

/-- `CategoryTheory.Adjunction.map_homEquiv_mapIso_trans_eqToIso_trans_hom_of_eq` with the source
of the transposed morphism given up to an equality of objects. -/
theorem _root_.CategoryTheory.Adjunction.map_homEquiv_heq_of_src_eq
    {C D E : Type*} [Category C] [Category D] [Category E] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) (F : C ⥤ E) {a₀ a a' b : C} (h₀ : a₀ = a)
    (e : a ≅ a') (h : a' = b) {c : D} (k : L.obj b ≅ c) {m : b ⟶ R.obj c}
    (hk : adj.homEquiv _ _ k.hom = m) (k₀ : L.obj a₀ ⟶ c)
    (hk₀ : HEq k₀ (L.mapIso e ≪≫ eqToIso (congrArg L.obj h) ≪≫ k).hom)
    {t : F.obj a ⟶ F.obj (R.obj c)}
    (ht : F.map e.hom ≫ eqToHom (congrArg F.obj h) ≫ F.map m = t) :
    HEq (F.map (adj.homEquiv a₀ c k₀)) t := by
  subst h₀
  cases hk₀
  rw [Adjunction.map_homEquiv_mapIso_trans_eqToIso_trans_hom_of_eq adj F e h k hk]
  exact heq_of_eq ht

/-- On sheaves of sets, the transpose along Stacks 03CZ of the identification of `g^*(A_mod)` with
the module underlying `g^*A` is the first inclusion `g⁻¹A ⟶ g^*A` of the pushout. -/
theorem moduleSheafFunctor_map_extendScalarsAdjunction_homEquiv_heq (g : Y ⟶ X)
    (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) :
    HEq ((Sheaf.moduleSheafFunctor.{u, u, u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
        ((ringSheafPullback B S hS g).obj (structureSheaf B S hS X.1 X.2)))).map
      ((Stacks.FlatChangeOfRings.extendScalarsAdjunction (structurePullbackMap B S hS g)).homEquiv
        ((inverseImageModules (smallEtaleRingedToposHom B S hS g).toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf (structureSheaf B S hS X.1 X.2))).obj
            A.underlyingModule) ((algebraPullback B S hS g).obj A).underlyingModule
        (underlyingModuleAlgebraPullbackModulePullbackIso B S hS g A).hom))
      ((sheafCompose (SmallEtale.topology B S hS Y.1) (forget CommRingCat.{u})).map
        ((algebraPullbackMap B S hS g).app A)) :=
  Adjunction.map_homEquiv_heq_of_src_eq
    (Stacks.FlatChangeOfRings.extendScalarsAdjunction (structurePullbackMap B S hS g))
    (Sheaf.moduleSheafFunctor.{u, u, u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
        ((ringSheafPullback B S hS g).obj (structureSheaf B S hS X.1 X.2))))
    (inverseImageModules_obj_underlyingModule_eq_domOf B S hS g A)
    (pullbackModuleObjRestrictScalarsIso
          (SmallEtale.topology B S hS Y.1)
          ((smallEtaleRingedToposHom B S hS g).toToposHom).inverseImage
          (Stacks.FlatChangeOfRings.ringSheafMap
            (O₁ := structureSheaf B S hS X.1 X.2) (O₂ := A.right) A.hom)
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf A.right))).symm
    (underlyingModule_inverseImageAlgebra B S hS g A).symm
    (underlyingModuleAlgebraPullbackIso B S hS g A).symm
    (Stacks.SheafOfModules.AlgebraPushout.homEquiv_extendScalarsComparison_anySite
      (structurePullbackMap B S hS g) (inverseImageAlgebra B S hS g A))
    (underlyingModuleAlgebraPullbackModulePullbackIso B S hS g A).hom HEq.rfl
    (Stacks.SheafOfModules.AlgebraPushout.moduleSheafFunctor_map_pullbackComparison_comp
      (smallEtaleRingedToposHom B S hS g).toToposHom A.hom (structurePullbackMap B S hS g)
      (underlyingModule_inverseImageAlgebra B S hS g A).symm)

/-- On sheaves of sets the transpose along Stacks 03D7 of a morphism `ε : g^*(A_mod) ⟶ P_mod` is
the transpose along Stacks 00YV of a morphism `k : g⁻¹A ⟶ P` as soon as their transposes along
Stacks 03CZ agree on sheaves of sets. -/
theorem moduleSheafFunctor_map_pullbackAdjPushforwardModules_homEquiv_heq_of (g : Y ⟶ X)
    (A : AlgebraSheaf.{u, u} B S hS X.1 X.2)
    {P : AlgebraSheaf.{u, u} B S hS Y.1 Y.2}
    (k : (ringSheafPullback B S hS g).obj A.right ⟶ P.right)
    (ε : (modulePullback B S hS g).obj A.underlyingModule ⟶ P.underlyingModule)
    (hinner : HEq ((Sheaf.moduleSheafFunctor.{u, u, u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
        ((ringSheafPullback B S hS g).obj (structureSheaf B S hS X.1 X.2)))).map
      ((Stacks.FlatChangeOfRings.extendScalarsAdjunction (structurePullbackMap B S hS g)).homEquiv
        ((inverseImageModules (smallEtaleRingedToposHom B S hS g).toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf (structureSheaf B S hS X.1 X.2))).obj
            A.underlyingModule) P.underlyingModule ε))
      ((sheafCompose (SmallEtale.topology B S hS Y.1) (forget CommRingCat.{u})).map k)) :
    HEq ((Sheaf.moduleSheafFunctor.{u, u, u + 1} (structureRingSheaf B S hS X)).map
      ((pullbackAdjPushforwardModules (smallEtaleRingedToposModulesHom B S hS g)).homEquiv
        A.underlyingModule P.underlyingModule ε))
      ((sheafCompose (SmallEtale.topology B S hS X.1) (forget CommRingCat.{u})).map
        ((commRingImageAdjunction (smallEtaleRingedToposHom B S hS g).toToposHom).homEquiv
          A.right P.right k)) := by
  have hflat := moduleSheafFunctor_map_pullbackAdjPushforwardModules_homEquiv_flat B S hS g ε
  simp only [smallEtaleRingedToposModulesHom,
    RingedToposHom.toRingedToposModulesHom_toToposHom] at hflat
  refine (heq_of_eq hflat).trans ?_
  refine HEq.trans ?_ (heq_of_eq (forget_map_commRingImageAdjunction_homEquiv
    (smallEtaleRingedToposHom B S hS g).toToposHom A.right P.right k)).symm
  exact Adjunction.homEquiv_heq_of_eq (smallEtaleRingedToposHom B S hS g).toToposHom.adj
    rfl rfl hinner

/-- On sheaves of sets, the transpose along Stacks 03D7 of the identification of `g^*(A_mod)` with
the module underlying `g^*A` is the transpose along Stacks 00YV of the pushout inclusion. -/
theorem moduleSheafFunctor_map_pullbackAdjPushforwardModules_homEquiv_heq (g : Y ⟶ X)
    (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) :
    HEq ((Sheaf.moduleSheafFunctor.{u, u, u + 1} (structureRingSheaf B S hS X)).map
      ((pullbackAdjPushforwardModules (smallEtaleRingedToposModulesHom B S hS g)).homEquiv
        A.underlyingModule ((algebraPullback B S hS g).obj A).underlyingModule
        (underlyingModuleAlgebraPullbackModulePullbackIso B S hS g A).hom))
      ((sheafCompose (SmallEtale.topology B S hS X.1) (forget CommRingCat.{u})).map
        ((commRingImageAdjunction (smallEtaleRingedToposHom B S hS g).toToposHom).homEquiv
          A.right ((algebraPullback B S hS g).obj A).right
          ((algebraPullbackMap B S hS g).app A))) :=
  moduleSheafFunctor_map_pullbackAdjPushforwardModules_homEquiv_heq_of B S hS g A
    ((algebraPullbackMap B S hS g).app A)
    (underlyingModuleAlgebraPullbackModulePullbackIso B S hS g A).hom
    (moduleSheafFunctor_map_extendScalarsAdjunction_homEquiv_heq B S hS g A)

/-- Heterogeneously equal morphisms of sheaves of sets agree on sections. -/
theorem _root_.CategoryTheory.Sheaf.hom_app_heq {C : Type*} [Category C]
    {J : GrothendieckTopology C}
    {P₁ P₂ Q₁ Q₂ : Sheaf J (Type u)} (hP : P₁ = P₂) (hQ : Q₁ = Q₂) {f₁ : P₁ ⟶ Q₁} {f₂ : P₂ ⟶ Q₂}
    (h : HEq f₁ f₂) (V : Cᵒᵖ) (x : P₁.obj.obj V) :
    HEq (f₁.hom.app V x)
      (f₂.hom.app V (cast (congrArg (fun P : Sheaf J (Type u) => P.obj.obj V) hP) x)) := by
  subst hP hQ
  cases h
  rfl

/-- `AlgebraicGeometry.Space.moduleSheafFunctor_map_pullbackAdjPushforwardModules_homEquiv_heq` on
sections. -/
theorem moduleSheafFunctor_map_pullbackAdjPushforwardModules_homEquiv_app (g : Y ⟶ X)
    (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) (V : (SmallEtale B S hS X.1)ᵒᵖ)
    (s : A.right.obj.obj V) :
    ((Sheaf.moduleSheafFunctor.{u, u, u + 1} (structureRingSheaf B S hS X)).map
      ((pullbackAdjPushforwardModules (smallEtaleRingedToposModulesHom B S hS g)).homEquiv
        A.underlyingModule ((algebraPullback B S hS g).obj A).underlyingModule
        (underlyingModuleAlgebraPullbackModulePullbackIso B S hS g A).hom)).hom.app V s =
      ((sheafCompose (SmallEtale.topology B S hS X.1) (forget CommRingCat.{u})).map
        ((commRingImageAdjunction (smallEtaleRingedToposHom B S hS g).toToposHom).homEquiv
          A.right ((algebraPullback B S hS g).obj A).right
          ((algebraPullbackMap B S hS g).app A))).hom.app V s :=
  eq_of_heq (Sheaf.hom_app_heq rfl rfl
    (moduleSheafFunctor_map_pullbackAdjPushforwardModules_homEquiv_heq B S hS g A) V s)

/-- A morphism `ε : g^*(A_mod) ⟶ P_mod` whose transpose along Stacks 03D7 agrees on sections with
the transpose along Stacks 00YV of `k : g⁻¹A ⟶ P` carries the chart section of `g^*(A_mod)` at `s`
to the chart projection of the transpose of `k` at `s`. -/
theorem chartSection_of_pullbackAdjPushforwardModules_homEquiv_app (g : Y ⟶ X)
    (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) {P : AlgebraSheaf.{u, u} B S hS Y.1 Y.2}
    (k : (ringSheafPullback B S hS g).obj A.right ⟶ P.right)
    (ε : (modulePullback B S hS g).obj A.underlyingModule ⟶ P.underlyingModule)
    (hset : ∀ (V : (SmallEtale B S hS X.1)ᵒᵖ) (s : A.right.obj.obj V),
      ((Sheaf.moduleSheafFunctor.{u, u, u + 1} (structureRingSheaf B S hS X)).map
        ((pullbackAdjPushforwardModules (smallEtaleRingedToposModulesHom B S hS g)).homEquiv
          A.underlyingModule P.underlyingModule ε)).hom.app V s =
        ((sheafCompose (SmallEtale.topology B S hS X.1) (forget CommRingCat.{u})).map
          ((commRingImageAdjunction (smallEtaleRingedToposHom B S hS g).toToposHom).homEquiv
            A.right P.right k)).hom.app V s)
    (d : ChartDiagram B S hS Y.1 X.1 g.hom) (s : A.right.obj.obj (op d.V)) :
    ε.val.app (op d.U) (modulePullbackChartSection B S hS g A.underlyingModule d s) =
      (moduleChartProjection B S hS g d.V (indexOfChartDiagram B S hS g d)).app
        ((smallEtaleRingedTopos B S hS Y).forgetRing.obj P.right)
        (((commRingImageAdjunction (smallEtaleRingedToposHom B S hS g).toToposHom).homEquiv
          A.right P.right k).hom.app (op d.V) s) := by
  have hunit := congrArg (fun m ↦ m.val.app (op d.V) s)
    (Adjunction.homEquiv_unit
      (pullbackAdjPushforwardModules (smallEtaleRingedToposModulesHom B S hS g))
      A.underlyingModule P.underlyingModule ε)
  refine Eq.trans (Functor.natTrans_app_map_apply
    (moduleChartProjection B S hS g d.V (indexOfChartDiagram B S hS g d))
    ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map ε)
    (((pullbackAdjPushforwardModules
        (smallEtaleRingedToposModulesHom B S hS g)).unit.app A.underlyingModule).val.app
      (op d.V) s)).symm ?_
  exact congrArg
    ((moduleChartProjection B S hS g d.V (indexOfChartDiagram B S hS g d)).app
      ((smallEtaleRingedTopos B S hS Y).forgetRing.obj P.right))
    (hunit.symm.trans (hset (op d.V) s))

/-- **The identification of `g^*(A_mod)` with the module underlying `g^*A` carries the chart
section of the pullback of modules to the ring-level chart section**: the chart projection of
the transpose along Stacks 00YV of the first inclusion `g⁻¹A ⟶ g^*A` of the pushout. -/
theorem underlyingModuleAlgebraPullbackModulePullbackIso_chartSection (g : Y ⟶ X)
    (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) (d : ChartDiagram B S hS Y.1 X.1 g.hom)
    (s : A.right.obj.obj (op d.V)) :
    (underlyingModuleAlgebraPullbackModulePullbackIso B S hS g A).hom.val.app (op d.U)
        (modulePullbackChartSection B S hS g A.underlyingModule d s) =
      (moduleChartProjection B S hS g d.V (indexOfChartDiagram B S hS g d)).app
        ((smallEtaleRingedTopos B S hS Y).forgetRing.obj ((algebraPullback B S hS g).obj A).right)
        ((((commRingImageAdjunction (smallEtaleRingedToposHom B S hS g).toToposHom).homEquiv _ _)
          ((algebraPullbackMap B S hS g).app A)).hom.app (op d.V) s) :=
  chartSection_of_pullbackAdjPushforwardModules_homEquiv_app B S hS g A
    ((algebraPullbackMap B S hS g).app A)
    (underlyingModuleAlgebraPullbackModulePullbackIso B S hS g A).hom
    (moduleSheafFunctor_map_pullbackAdjPushforwardModules_homEquiv_app B S hS g A) d s

end AlgebraicGeometry.Space

end
