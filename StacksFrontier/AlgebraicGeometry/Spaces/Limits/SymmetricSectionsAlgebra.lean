module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.SectionwiseSymmetricAlgebraRing
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafImageQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AlgebraSheafIdealQuotient

/-!
# The symmetric algebra of a module on an algebraic space, sheafified from its sections

Let `X` be an algebraic space over a scheme `S` and `𝒢` an `𝒪_X`-module.  This file builds the
algebra sheaf `Sym(𝒢)` on the small étale site of `X` as the sheafification of the presheaf of
commutative rings `U ↦ Sym_{𝒪_X(U)}(𝒢(U))`, with

* its degree-one generator `𝒢 ⟶ Sym(𝒢)`, a morphism of `𝒪_X`-modules;
* its universal property: a morphism of `𝒪_X`-modules `𝒢 ⟶ 𝒜` into the underlying module of an
  algebra sheaf `𝒜` extends uniquely to a morphism of algebra sheaves `Sym(𝒢) ⟶ 𝒜`;
* its functoriality in `𝒢`.

The point of building it from the *ungraded* sectionwise symmetric algebra is that its sections
over an affine étale chart can be computed: see
`StacksFrontier.AlgebraicGeometry.Spaces.Limits.SymmetricSectionsAlgebraAffine`.

## Main definitions

* `AlgebraicGeometry.Space.SymSections.algebra`: the algebra sheaf `Sym(𝒢)`.
* `AlgebraicGeometry.Space.SymSections.gen`: its degree-one generator.
* `AlgebraicGeometry.Space.SymSections.lift`: the morphism `Sym(𝒢) ⟶ 𝒜` extending `𝒢 ⟶ 𝒜`.
* `AlgebraicGeometry.Space.SymSections.map`: the morphism `Sym(𝒢) ⟶ Sym(𝒢')` induced by
  `𝒢 ⟶ 𝒢'`.

## Main results

* `AlgebraicGeometry.Space.SymSections.gen_lift`: the lift restricts to the given morphism on the
  generator.
* `AlgebraicGeometry.Space.SymSections.hom_ext`: morphisms out of `Sym(𝒢)` are determined by
  their values on the generator.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

namespace SymSections

variable (G : Modules.{u, u} B S hS F hF)

/-- The presheaf of modules underlying `G`, over the presheaf of commutative rings of global
functions on the étale charts. -/
abbrev val' : PresheafOfModules.{u} (structurePresheaf B S hS F ⋙ forget₂ CommRingCat RingCat) :=
  G.val

/-- The presheaf `U ↦ Sym_{𝒪(U)}(G(U))`. -/
noncomputable abbrev presheaf : (SmallEtale B S hS F)ᵒᵖ ⥤ CommRingCat.{u} :=
  PresheafOfModules.sectionwiseSymAlg (val' G)

/-- The sheaf of rings `Sym(G)`: the sheafification of `U ↦ Sym_{𝒪(U)}(G(U))`. -/
noncomputable def ringSheaf : Sheaf (SmallEtale.topology B S hS F) CommRingCat.{u} :=
  (presheafToSheaf _ _).obj (presheaf G)

/-- The structure map `𝒪 ⟶ Sym(G)`. -/
noncomputable def structureHom : structureSheaf B S hS F hF ⟶ ringSheaf G :=
  ⟨PresheafOfModules.toSymAlg (val' G) ≫ toSheafify _ (presheaf G)⟩

/-- **The symmetric algebra `Sym(G)` of an `𝒪`-module on an algebraic space**, as an algebra
sheaf: the sheafified sectionwise symmetric algebra. -/
noncomputable def algebra : AlgebraSheaf.{u, u} B S hS F hF :=
  AlgebraSheaf.ofHom (structureHom G)

/-- The sheaf of rings underlying `algebra G` is `ringSheaf G`. -/
theorem algebra_right : (algebra G).right = ringSheaf G := rfl

/-- The structure map of `algebra G` on sections over `U` sends `r` to the image under the
sheafification unit of the image of `r` in `Sym_{𝒪(U)}(G(U))`. -/
theorem algebra_algebraMap (U : (SmallEtale B S hS F)ᵒᵖ) (r : (structurePresheaf B S hS F).obj U) :
    (algebra G).algebraMap U r =
      (toSheafify _ (presheaf G)).app U ((PresheafOfModules.toSymAlg (val' G)).app U r) :=
  rfl

/-- The sheafification unit `Sym_{𝒪(U)}(G(U)) ⟶ Sym(G)(U)`. -/
noncomputable abbrev unit : presheaf G ⟶ (ringSheaf G).obj :=
  toSheafify _ (presheaf G)

/-! ### The generator -/

/-- The degree-one generator on sections, `m ↦ ι m` followed by the sheafification unit. -/
noncomputable def genApp (U : (SmallEtale B S hS F)ᵒᵖ) (m : (val' G).obj U) :
    (ringSheaf G).obj.obj U :=
  (unit G).app U (SymmetricAlgebra.ι
    ((structurePresheaf B S hS F ⋙ forget₂ CommRingCat RingCat).obj U) ((val' G).obj U) m)

/-- The generator on sections commutes with restriction along `f : U ⟶ V`. -/
theorem genApp_map {U V : (SmallEtale B S hS F)ᵒᵖ} (f : U ⟶ V) (m : (val' G).obj U) :
    genApp G V ((val' G).map f m) = (ringSheaf G).obj.map f (genApp G U m) :=
  (congrArg ((unit G).app V) (PresheafOfModules.sectionwiseSymAlg_map_ι (val' G) f m)).symm.trans
    (ConcreteCategory.congr_hom ((unit G).naturality f) _)

/-- The generator on sections is `𝒪(U)`-linear: `genApp G U (r • m)` is the product of the
image of `r` with `genApp G U m`. -/
theorem genApp_smul (U : (SmallEtale B S hS F)ᵒᵖ)
    (r : (structurePresheaf B S hS F ⋙ forget₂ CommRingCat RingCat).obj U)
    (m : (val' G).obj U) :
    genApp G U (r • m) =
      (unit G).app U ((PresheafOfModules.toSymAlg (val' G)).app U r) * genApp G U m := by
  have h : SymmetricAlgebra.ι ((structurePresheaf B S hS F ⋙ forget₂ CommRingCat RingCat).obj U)
        ((val' G).obj U) (r • m) =
      algebraMap ((structurePresheaf B S hS F ⋙ forget₂ CommRingCat RingCat).obj U)
        (SymmetricAlgebra ((structurePresheaf B S hS F ⋙ forget₂ CommRingCat RingCat).obj U)
          ((val' G).obj U)) r *
        SymmetricAlgebra.ι ((structurePresheaf B S hS F ⋙ forget₂ CommRingCat RingCat).obj U)
          ((val' G).obj U) m := by
    rw [map_smul, Algebra.smul_def]
  exact (congrArg ((unit G).app U) h).trans (map_mul _ _ _)

/-- The presheaf map underlying the generator. -/
noncomputable def genPresheaf :
    (val' G).presheaf ⟶ (AlgebraSheaf.underlyingModule (algebra G)).val.presheaf where
  app U := AddCommGrpCat.ofHom
    { toFun := genApp G U
      map_zero' := (congrArg ((unit G).app U) (map_zero _)).trans (map_zero _)
      map_add' := fun m m' => (congrArg ((unit G).app U) (map_add _ m m')).trans
        (map_add _ _ _) }
  naturality {U V} f := by
    ext m
    exact genApp_map G f m

/-- **The degree-one generator `G ⟶ Sym(G)`**, as a morphism of `𝒪`-modules. -/
noncomputable def gen : G ⟶ AlgebraSheaf.underlyingModule (algebra G) :=
  show SheafOfModules.Hom _ _ from
  { val := PresheafOfModules.homMk (M₁ := val' G) (genPresheaf G) fun U r m =>
      genApp_smul G U r m }

/-- On sections over `U`, the generator `gen G` sends `m` to `genApp G U m`. -/
theorem gen_val_app_apply (U : (SmallEtale B S hS F)ᵒᵖ) (m : (val' G).obj U) :
    (gen G).val.app U m = genApp G U m :=
  rfl

/-! ### The universal property -/

variable {G} {𝒜 : AlgebraSheaf.{u, u} B S hS F hF}

/-- The sectionwise linear maps `G(U) ⟶ 𝒜(U)` underlying a morphism of modules. -/
noncomputable def liftLinear (ψ : G ⟶ AlgebraSheaf.underlyingModule 𝒜)
    (U : (SmallEtale B S hS F)ᵒᵖ) :
    letI := PresheafOfModules.algebraOfHom (O := structurePresheaf B S hS F) (𝒜.hom.hom) U
    (val' G).obj U →ₗ[(structurePresheaf B S hS F ⋙ forget₂ CommRingCat RingCat).obj U]
      𝒜.right.obj.obj U :=
  letI := PresheafOfModules.algebraOfHom (O := structurePresheaf B S hS F) (𝒜.hom.hom) U
  { toFun := fun (m : (val' G).obj U) => ψ.val.app U m
    map_add' := fun m m' => map_add (ψ.val.app U).hom m m'
    map_smul' := fun r m => (ψ.val.app U).hom.map_smul r m }

/-- The presheaf map `Sym_{𝒪(U)}(G(U)) ⟶ 𝒜(U)` extending `ψ`. -/
noncomputable def liftPresheaf (ψ : G ⟶ AlgebraSheaf.underlyingModule 𝒜) :
    presheaf G ⟶ 𝒜.right.obj :=
  PresheafOfModules.symAlgLift (O := structurePresheaf B S hS F) (𝒜.hom.hom) (liftLinear ψ)
    fun f m => (PresheafOfModules.naturality_apply ψ.val f m).symm

/-- **The morphism of algebra sheaves `Sym(G) ⟶ 𝒜` extending `ψ : G ⟶ 𝒜`.** -/
noncomputable def lift (ψ : G ⟶ AlgebraSheaf.underlyingModule 𝒜) : algebra G ⟶ 𝒜 where
  right := ⟨sheafifyLift _ (liftPresheaf ψ) 𝒜.right.property⟩
  comm U r :=
    (ConcreteCategory.congr_hom (congrArg (fun k => k.app U)
      (toSheafify_sheafifyLift _ (liftPresheaf ψ) 𝒜.right.property)) _).trans
      (ConcreteCategory.congr_hom (congrArg (fun k => k.app U)
        (PresheafOfModules.toSymAlg_symAlgLift (O := structurePresheaf B S hS F) (𝒜.hom.hom)
          (liftLinear ψ) fun f m => (PresheafOfModules.naturality_apply ψ.val f m).symm)) r)

variable (ψ : G ⟶ AlgebraSheaf.underlyingModule 𝒜)

/-- On the image of the sheafification unit, `lift ψ` agrees with `liftPresheaf ψ`. -/
theorem lift_right_app_unit (U : (SmallEtale B S hS F)ᵒᵖ) (x : (presheaf G).obj U) :
    (lift ψ).right.hom.app U ((unit G).app U x) = (liftPresheaf ψ).app U x :=
  ConcreteCategory.congr_hom (congrArg (fun k => k.app U)
    (toSheafify_sheafifyLift _ (liftPresheaf ψ) 𝒜.right.property)) x

/-- On sections over `U`, `lift ψ` sends the generator `genApp G U m` to `ψ m`. -/
theorem gen_lift_apply (U : (SmallEtale B S hS F)ᵒᵖ) (m : (val' G).obj U) :
    (lift ψ).right.hom.app U (genApp G U m) = ψ.val.app U m :=
  (lift_right_app_unit ψ U _).trans
    (PresheafOfModules.symAlgLift_app_ι (O := structurePresheaf B S hS F) (𝒜.hom.hom)
      (liftLinear ψ) (fun f m => (PresheafOfModules.naturality_apply ψ.val f m).symm) U m)

/-- **The lift restricts to the given morphism on the generator.** -/
theorem gen_lift : gen G ≫ AlgebraSheaf.underlyingModuleMap (lift ψ) = ψ :=
  SheafOfModules.hom_ext <| PresheafOfModules.hom_ext fun U =>
    ModuleCat.hom_ext <| LinearMap.ext <| gen_lift_apply ψ U

variable (G) in
/-- **Morphisms out of `Sym(G)` are determined by their values on the generator.** -/
theorem hom_ext {g g' : algebra G ⟶ 𝒜}
    (h : ∀ (U : (SmallEtale B S hS F)ᵒᵖ) (m : (val' G).obj U),
      g.right.hom.app U (genApp G U m) = g'.right.hom.app U (genApp G U m)) :
    g = g' := by
  refine AlgebraSheaf.Hom.ext (Sheaf.hom_ext ?_)
  refine sheafify_hom_ext _ _ _ 𝒜.right.property ?_
  refine PresheafOfModules.sectionwiseSymAlg_hom_ext ?_ h
  refine NatTrans.ext (funext fun U => CommRingCat.hom_ext (RingHom.ext fun r => ?_))
  exact (g.comm U r).trans (g'.comm U r).symm

/-! ### Functoriality -/

/-- **The morphism `Sym(G) ⟶ Sym(G')` induced by `φ : G ⟶ G'`.** -/
noncomputable def map {G G' : Modules.{u, u} B S hS F hF} (φ : G ⟶ G') :
    algebra G ⟶ algebra G' :=
  lift (φ ≫ gen G')

/-- On sections over `U`, `map φ` sends the generator `genApp G U m` to `genApp G' U (φ m)`. -/
theorem map_genApp {G G' : Modules.{u, u} B S hS F hF} (φ : G ⟶ G')
    (U : (SmallEtale B S hS F)ᵒᵖ) (m : (val' G).obj U) :
    (map φ).right.hom.app U (genApp G U m) = genApp G' U (φ.val.app U m) :=
  gen_lift_apply (φ ≫ gen G') U m

/-- The generators intertwine `φ` and `map φ`: `gen G ≫ map φ = φ ≫ gen G'`. -/
theorem gen_map {G G' : Modules.{u, u} B S hS F hF} (φ : G ⟶ G') :
    gen G ≫ AlgebraSheaf.underlyingModuleMap (map φ) = φ ≫ gen G' :=
  gen_lift _

/-- `map` sends the identity of `G` to the identity of `Sym(G)`. -/
theorem map_id (G : Modules.{u, u} B S hS F hF) : map (𝟙 G) = 𝟙 (algebra G) :=
  hom_ext G fun U m => map_genApp (𝟙 G) U m

/-- `map` is compatible with composition. -/
theorem map_comp {G G' G'' : Modules.{u, u} B S hS F hF} (φ : G ⟶ G') (φ' : G' ⟶ G'') :
    map (φ ≫ φ') = map φ ≫ map φ' :=
  hom_ext G fun U m => (map_genApp (φ ≫ φ') U m).trans
    ((map_genApp φ' U (φ.val.app U m)).symm.trans
      (congrArg ((map φ').right.hom.app U) (map_genApp φ U m)).symm)

/-- Precomposing `lift ψ'` with `map φ` gives the lift of `φ ≫ ψ'`. -/
theorem map_lift {G G' : Modules.{u, u} B S hS F hF} (φ : G ⟶ G')
    (ψ' : G' ⟶ AlgebraSheaf.underlyingModule 𝒜) :
    map φ ≫ lift ψ' = lift (φ ≫ ψ') :=
  hom_ext G fun U m =>
    ((congrArg ((lift ψ').right.hom.app U) (map_genApp φ U m)).trans
      (gen_lift_apply ψ' U (φ.val.app U m))).trans (gen_lift_apply (φ ≫ ψ') U m).symm

end SymSections

end AlgebraicGeometry.Space

end
