module

public import StacksFrontier.AlgebraicGeometry.ConormalAffineCotangent.Sections
public import StacksFrontier.AlgebraicGeometry.ConormalComparison.IdealSheafComparison
public import StacksFrontier.AlgebraicGeometry.ConormalSheaf.Basic
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.ImmersionStalk
public import StacksFrontier.AlgebraicGeometry.RingedSpace.IdealSheafGenerators
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackStalkAdjunction

/-!
# The stalk of the conormal sheaf of an immersion

Let `j : Z ⟶ X` be an immersion of schemes and `z : Z`.  Write `g = j.liftCoborder` for the
canonical closed immersion of `Z` into the coborder neighbourhood of the image of `j`, and let
`I` be the kernel of the surjection `𝒪_{coborder, g z} ⟶ 𝒪_{Z,z}` of local rings.  The stalk at
`z` of the conormal sheaf of `j` is the cotangent module `I/I²`.

## Main definitions

* `Stacks.Conormal.stalkModule`, with its two instances
  `Stacks.Conormal.idealSheafStalkModule` and `Stacks.Conormal.conormalSheafStalkModule`: the
  module structure of [Stacks, Tag 01CB] on the stalk of a presheaf of modules over the
  structure sheaf of a scheme.
* `Stacks.Conormal.cotangentStalkModule`: the module structure on `I/I²` over `𝒪_{Z,z}`,
  obtained from the identification of `𝒪_{Z,z}` with the quotient of `𝒪_{coborder, g z}` by `I`.
* `Stacks.Conormal.idealSection`: the image in the structure sheaf of a section of the ideal
  sheaf of a morphism of schemes.
* `Stacks.Conormal.conormalSheafStalkEquivCotangent`: the identification `(C_{Z/X})_z ≅ I/I²`,
  linear over `𝒪_{Z,z}`.

## Main results

* `Stacks.Conormal.germ_idealSection_mem_ker_stalkMap`: the germ at `g z` of a section of the
  ideal sheaf of `g` lies in `I`.
* `Stacks.Conormal.conormalSheafStalkEquivCotangent_germ`: the identification carries the germ
  at `z` of the conormal class of a section of the ideal sheaf to the class modulo `I²` of the
  germ of that section.  This pins the identification down.

## Implementation notes

The conormal sheaf is the module pullback along `g` of the ideal sheaf of `g`, so its stalk is
the base change `𝒪_{Z,z} ⊗ I_{g z}` of the stalk of the ideal sheaf; the conormal class of a
section is the image of that section under the unit of the pullback–pushforward adjunction, and
the base-change identification is normalised by sending the germ of such an image to `1 ⊗ germ`.
Composing with `𝒪_{Z,z} ⊗_{𝒪_{coborder, g z}} I ≅ I/I²` gives the statement.

The structure sheaf of a scheme is a presheaf of commutative rings while a sheaf of modules is
indexed by the associated presheaf of rings, and the two spellings agree only at default
transparency; the module structures on the stalks are therefore named and declared as local
instances rather than left to instance search.

## References

* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open scoped TensorProduct

universe u

namespace Stacks.Conormal

/-- The `𝒪_{Y,y}`-module structure of [Stacks, Tag 01CB] on the stalk at `y` of a presheaf of
`𝒪_Y`-modules on a scheme `Y`. -/
abbrev stalkModule {Y : Scheme.{u}}
    (M : PresheafOfModules.{u} (Y.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u})) (y : Y) :
    Module (ToType (Y.presheaf.stalk y))
      (ToType (TopCat.Presheaf.stalk (C := Ab.{u}) M.presheaf y)) :=
  inferInstance

/-- The stalk at a point of `W` of the ideal sheaf of a morphism of schemes `g : Z ⟶ W` is a
module over the local ring of `W` at that point. -/
abbrev idealSheafStalkModule {Z W : Scheme.{u}} (g : Z ⟶ W) (w : W) :
    Module (ToType (W.presheaf.stalk w))
      (ToType (TopCat.Presheaf.stalk (C := Ab.{u})
        (Stacks.ClosedImmersion.idealSheaf g.toLRSHom.toShHom).val.presheaf w)) :=
  stalkModule (Y := W)
    (M := (Stacks.ClosedImmersion.idealSheaf g.toLRSHom.toShHom).val) w

/-- The stalk at `z` of the conormal sheaf of an immersion `j : Z ⟶ X` is a module over the
local ring of `Z` at `z`. -/
abbrev conormalSheafStalkModule {Z X : Scheme.{u}} (j : Z ⟶ X) [IsImmersion j] (z : Z) :
    Module (ToType (Z.presheaf.stalk z))
      (ToType (TopCat.Presheaf.stalk (C := Ab.{u}) (conormalSheaf j).val.presheaf z)) :=
  stalkModule (Y := Z) (M := (conormalSheaf j).val) z

attribute [local instance] idealSheafStalkModule conormalSheafStalkModule

/-! ### The base change of the kernel of a surjection -/

section Algebra

variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) (hφ : Function.Surjective φ)

/-- The target of a surjective ring homomorphism is the quotient by its kernel, as a module
over the source. -/
private def targetQuotLinearEquiv :
    letI : Algebra R S := φ.toAlgebra
    S ≃ₗ[R] R ⧸ RingHom.ker φ := by
  letI : Algebra R S := φ.toAlgebra
  refine
    { __ := (RingHom.quotientKerEquivOfSurjective hφ).symm.toAddEquiv
      map_smul' := ?_ }
  intro r s
  obtain ⟨a, rfl⟩ := hφ s
  change (RingHom.quotientKerEquivOfSurjective hφ).symm (r • φ a) =
    r • (RingHom.quotientKerEquivOfSurjective hφ).symm (φ a)
  rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, ← map_mul,
    RingHom.quotientKerEquivOfSurjective_symm_apply,
    RingHom.quotientKerEquivOfSurjective_symm_apply, map_mul, Algebra.smul_def,
    Ideal.Quotient.algebraMap_eq]

/-- **The base change of the kernel of a surjection is its cotangent module.** For a surjective
ring homomorphism `φ : R → S` with kernel `I`, the `S`-module `S ⊗_R I` is `I/I²`. -/
private def tensorKerEquivCotangent :
    letI : Algebra R S := φ.toAlgebra
    letI : Module S (RingHom.ker φ).Cotangent :=
      Module.compHom (RingHom.ker φ).Cotangent
        (RingHom.quotientKerEquivOfSurjective hφ).symm.toRingHom
    TensorProduct R S (RingHom.ker φ) ≃ₗ[S] (RingHom.ker φ).Cotangent := by
  letI : Algebra R S := φ.toAlgebra
  letI : Module S (RingHom.ker φ).Cotangent :=
    Module.compHom (RingHom.ker φ).Cotangent
      (RingHom.quotientKerEquivOfSurjective hφ).symm.toRingHom
  have hsmulS : ∀ (r : R) (s : S), (φ r) • s = r • s := by
    intro r s
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
    rfl
  have hsmulT : ∀ (r : R) (t : TensorProduct R S (RingHom.ker φ)), (φ r) • t = r • t := by
    intro r t
    induction t using TensorProduct.inductionOn with
    | tmul s a => rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', hsmulS]
    | add x y hx hy => rw [smul_add, smul_add, hx, hy]
  have hsmulC : ∀ (r : R) (c : (RingHom.ker φ).Cotangent), (φ r) • c = r • c := by
    intro r c
    change (RingHom.quotientKerEquivOfSurjective hφ).symm (φ r) • c = r • c
    rw [RingHom.quotientKerEquivOfSurjective_symm_apply, ← Ideal.Quotient.algebraMap_eq,
      algebraMap_smul]
  refine
    { __ := ((TensorProduct.congr (targetQuotLinearEquiv φ hφ)
        (LinearEquiv.refl R (RingHom.ker φ))).trans
          ((RingHom.ker φ).quotTensorEquivCotangent.restrictScalars R)).toAddEquiv
      map_smul' := ?_ }
  intro s t
  obtain ⟨r, rfl⟩ := hφ s
  change ((TensorProduct.congr (targetQuotLinearEquiv φ hφ)
      (LinearEquiv.refl R (RingHom.ker φ))).trans
        ((RingHom.ker φ).quotTensorEquivCotangent.restrictScalars R)) (φ r • t) =
    φ r • ((TensorProduct.congr (targetQuotLinearEquiv φ hφ)
      (LinearEquiv.refl R (RingHom.ker φ))).trans
        ((RingHom.ker φ).quotTensorEquivCotangent.restrictScalars R)) t
  rw [hsmulT, hsmulC, LinearEquiv.map_smul]

/-- The base change identification carries `1 ⊗ a` to the class of `a` modulo `I²`. -/
private theorem tensorKerEquivCotangent_one_tmul (a : RingHom.ker φ) :
    letI : Algebra R S := φ.toAlgebra
    letI : Module S (RingHom.ker φ).Cotangent :=
      Module.compHom (RingHom.ker φ).Cotangent
        (RingHom.quotientKerEquivOfSurjective hφ).symm.toRingHom
    tensorKerEquivCotangent φ hφ ((1 : S) ⊗ₜ[R] a) = (RingHom.ker φ).toCotangent a :=
  (congrArg (fun y : R ⧸ RingHom.ker φ =>
      (RingHom.ker φ).quotTensorEquivCotangent (y ⊗ₜ[R] a))
    (map_one (RingHom.quotientKerEquivOfSurjective hφ).symm)).trans
    ((RingHom.ker φ).quotTensorEquivCotangent_one_tmul a)

end Algebra

/-! ### The stalk of the ideal sheaf of a morphism of schemes -/

section IdealStalk

variable {Z W : Scheme.{u}} (g : Z ⟶ W)

/-- The image in `𝒪_W` of a section of the ideal sheaf of `g` over an open set. -/
abbrev idealSection (V : W.Opens)
    (s : (Stacks.ClosedImmersion.idealSheaf g.toLRSHom.toShHom).val.obj (op V)) :
    ToType (W.presheaf.obj (op V)) :=
  (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
    (structureSheafHom g.toLRSHom.toShHom))).val.app (op V) s

/-- **The germ of a section of the ideal sheaf lies in the kernel of the stalk map.** -/
theorem germ_idealSection_mem_ker_stalkMap (z : Z) (V : W.Opens) (hz : g.base z ∈ V)
    (s : (Stacks.ClosedImmersion.idealSheaf g.toLRSHom.toShHom).val.obj (op V)) :
    (W.presheaf.germ V (g.base z) hz) (idealSection g V s) ∈
      RingHom.ker (g.stalkMap z).hom := by
  refine RingHom.mem_ker.mpr ?_
  rw [Scheme.Hom.germ_stalkMap_apply]
  have h := Stacks.Conormal.AffineCotangent.Sections.app_idealSheaf_section_eq_zero g V s
  simp [h]

/-- Taking the image in `𝒪_W` is compatible with restriction. -/
private theorem idealSection_map {V V' : W.Opens} (i : V' ⟶ V)
    (s : (Stacks.ClosedImmersion.idealSheaf g.toLRSHom.toShHom).val.obj (op V)) :
    idealSection g V'
        ((Stacks.ClosedImmersion.idealSheaf g.toLRSHom.toShHom).val.map i.op s) =
      W.presheaf.map i.op (idealSection g V s) :=
  PresheafOfModules.naturality_apply
    (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
      (structureSheafHom g.toLRSHom.toShHom))).val i.op s

/-- Taking germs of the image in `𝒪_W` is compatible with restriction. -/
private theorem germ_idealSection_map (w : W) {V V' : W.Opens} (i : V' ⟶ V) (hV' : w ∈ V')
    (s : (Stacks.ClosedImmersion.idealSheaf g.toLRSHom.toShHom).val.obj (op V)) :
    (W.presheaf.germ V' w hV')
        (idealSection g V'
          ((Stacks.ClosedImmersion.idealSheaf g.toLRSHom.toShHom).val.map i.op s)) =
      (W.presheaf.germ V w (i.le hV')) (idealSection g V s) :=
  (congrArg (W.presheaf.germ V' w hV') (idealSection_map g i s)).trans
    (TopCat.Presheaf.germ_res_apply W.presheaf i w hV' (idealSection g V s))

/-- The structure sheaf stalk, as a cocone over the diagram computing the stalk of the ideal
sheaf: a section is sent to the germ of its image in `𝒪_W`. -/
private def idealStalkCocone (w : W) :
    Cocone ((OpenNhds.inclusion w).op ⋙
      (Stacks.ClosedImmersion.idealSheaf g.toLRSHom.toShHom).val.presheaf) where
  pt := AddCommGrpCat.of (ToType (W.presheaf.stalk w))
  ι :=
    { app := fun V => AddCommGrpCat.ofHom
        (AddMonoidHom.mk'
          (fun s => (W.presheaf.germ V.unop.1 w V.unop.2) (idealSection g V.unop.1 s))
          (fun a b => by
            refine Eq.trans (congrArg (W.presheaf.germ V.unop.1 w V.unop.2)
              (map_add ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
                (structureSheafHom g.toLRSHom.toShHom))).val.app (op V.unop.1)).hom a b)) ?_
            exact map_add (W.presheaf.germ V.unop.1 w V.unop.2).hom _ _))
      naturality := by
        intro V V' f
        ext s
        exact germ_idealSection_map g w ((OpenNhds.inclusion w).map f.unop) V'.unop.2 s }

/-- **The germ of the image in `𝒪_W` of a section of the ideal sheaf**, as a homomorphism out
of the stalk of the ideal sheaf. -/
private def idealStalkHom (w : W) :
    ToType (TopCat.Presheaf.stalk (C := Ab.{u})
        (Stacks.ClosedImmersion.idealSheaf g.toLRSHom.toShHom).val.presheaf w) →+
      ToType (W.presheaf.stalk w) :=
  (colimit.desc _ (idealStalkCocone g w)).hom

private theorem idealStalkHom_germ (w : W) (V : W.Opens) (hw : w ∈ V)
    (s : (Stacks.ClosedImmersion.idealSheaf g.toLRSHom.toShHom).val.obj (op V)) :
    idealStalkHom g w (TopCat.Presheaf.germ (C := Ab.{u})
        (Stacks.ClosedImmersion.idealSheaf g.toLRSHom.toShHom).val.presheaf V w hw s) =
      (W.presheaf.germ V w hw) (idealSection g V s) :=
  ConcreteCategory.congr_hom
    (colimit.ι_desc (idealStalkCocone g w) (op (⟨V, hw⟩ : OpenNhds w))) s

private theorem idealStalkHom_smul (w : W) (r : ToType (W.presheaf.stalk w))
    (m : ToType (TopCat.Presheaf.stalk (C := Ab.{u})
      (Stacks.ClosedImmersion.idealSheaf g.toLRSHom.toShHom).val.presheaf w)) :
    idealStalkHom g w (r • m) = r * idealStalkHom g w m := by
  obtain ⟨V₁, hV₁, r₀, hr⟩ := TopCat.Presheaf.exists_germ_eq W.presheaf r
  obtain ⟨V₂, hV₂, m₀, hm⟩ := TopCat.Presheaf.exists_germ_eq
    (Stacks.ClosedImmersion.idealSheaf g.toLRSHom.toShHom).val.presheaf m
  have hmem : w ∈ V₁ ⊓ V₂ := ⟨hV₁, hV₂⟩
  set r₁ := W.presheaf.map (homOfLE (inf_le_left (a := V₁) (b := V₂))).op r₀ with hr₁
  set m₁ := (Stacks.ClosedImmersion.idealSheaf g.toLRSHom.toShHom).val.presheaf.map
    (homOfLE (inf_le_right (a := V₁) (b := V₂))).op m₀ with hm₁
  have hr' : (W.presheaf.germ (V₁ ⊓ V₂) w hmem) r₁ = r :=
    (TopCat.Presheaf.germ_res_apply W.presheaf (homOfLE inf_le_left) w hmem r₀).trans hr
  have hm' : TopCat.Presheaf.germ (C := Ab.{u})
      (Stacks.ClosedImmersion.idealSheaf g.toLRSHom.toShHom).val.presheaf (V₁ ⊓ V₂) w hmem m₁
        = m :=
    (TopCat.Presheaf.germ_res_apply
      (Stacks.ClosedImmersion.idealSheaf g.toLRSHom.toShHom).val.presheaf
      (homOfLE inf_le_right) w hmem m₀).trans hm
  rw [← hr', ← hm']
  refine Eq.trans (congrArg (idealStalkHom g w)
    (PresheafOfModules.germ_smul (R := W.presheaf)
      (Stacks.ClosedImmersion.idealSheaf g.toLRSHom.toShHom).val w (V₁ ⊓ V₂) hmem r₁ m₁).symm) ?_
  refine Eq.trans (idealStalkHom_germ g w (V₁ ⊓ V₂) hmem _) ?_
  refine Eq.trans (congrArg (W.presheaf.germ (V₁ ⊓ V₂) w hmem)
    (((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
      (structureSheafHom g.toLRSHom.toShHom))).val.app (op (V₁ ⊓ V₂))).hom.map_smul r₁ m₁)) ?_
  refine Eq.trans (map_mul (W.presheaf.germ (V₁ ⊓ V₂) w hmem).hom r₁
    (idealSection g (V₁ ⊓ V₂) m₁)) ?_
  exact congrArg (fun y => (W.presheaf.germ (V₁ ⊓ V₂) w hmem) r₁ * y)
    (idealStalkHom_germ g w (V₁ ⊓ V₂) hmem m₁).symm

private theorem idealStalkHom_injective (w : W) : Function.Injective (idealStalkHom g w) := by
  rw [injective_iff_map_eq_zero]
  intro ξ hξ
  obtain ⟨V, hV, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq
    (Stacks.ClosedImmersion.idealSheaf g.toLRSHom.toShHom).val.presheaf ξ
  have hξ' : (W.presheaf.germ V w hV) (idealSection g V s) = 0 :=
    (idealStalkHom_germ g w V hV s).symm.trans hξ
  have hzero : (W.presheaf.germ V w hV) (idealSection g V s) =
      (W.presheaf.germ V w hV) (0 : ToType (W.presheaf.obj (op V))) :=
    hξ'.trans (map_zero (W.presheaf.germ V w hV).hom).symm
  obtain ⟨V', hV', i, i', hres⟩ :=
    W.presheaf.germ_eq w hV hV (idealSection g V s) 0 hzero
  have hres' : idealSection g V'
      ((Stacks.ClosedImmersion.idealSheaf g.toLRSHom.toShHom).val.map i.op s) = 0 :=
    (idealSection_map g i s).trans (hres.trans (map_zero (W.presheaf.map i'.op).hom))
  have hs0 : (Stacks.ClosedImmersion.idealSheaf g.toLRSHom.toShHom).val.map i.op s = 0 :=
    Stacks.Conormal.Locality.idealSheaf_section_injective g V'
      (hres'.trans (map_zero ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom g.toLRSHom.toShHom))).val.app (op V')).hom).symm)
  have hres2 := TopCat.Presheaf.germ_res_apply
    (Stacks.ClosedImmersion.idealSheaf g.toLRSHom.toShHom).val.presheaf i w hV' s
  refine hres2.symm.trans ?_
  refine Eq.trans (congrArg (TopCat.Presheaf.germ (C := Ab.{u})
    (Stacks.ClosedImmersion.idealSheaf g.toLRSHom.toShHom).val.presheaf V' w hV') hs0) ?_
  exact map_zero (TopCat.Presheaf.germ (C := Ab.{u})
    (Stacks.ClosedImmersion.idealSheaf g.toLRSHom.toShHom).val.presheaf V' w hV').hom

private theorem idealStalkHom_mem_ker [IsImmersion g] (z : Z)
    (ξ : ToType (TopCat.Presheaf.stalk (C := Ab.{u})
      (Stacks.ClosedImmersion.idealSheaf g.toLRSHom.toShHom).val.presheaf (g.base z))) :
    idealStalkHom g (g.base z) ξ ∈ RingHom.ker (g.stalkMap z).hom := by
  obtain ⟨V, hz, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq
    (Stacks.ClosedImmersion.idealSheaf g.toLRSHom.toShHom).val.presheaf ξ
  exact Eq.mpr (congrArg (fun y => y ∈ RingHom.ker (g.stalkMap z).hom)
      (idealStalkHom_germ g (g.base z) V hz s))
    (germ_idealSection_mem_ker_stalkMap g z V hz s)

private theorem exists_idealStalkHom_eq [IsImmersion g] (z : Z)
    (a : ToType (W.presheaf.stalk (g.base z))) (ha : a ∈ RingHom.ker (g.stalkMap z).hom) :
    ∃ ξ, idealStalkHom g (g.base z) ξ = a := by
  rw [← Stacks.AlgebraicGeometry.RegularIdealSheaf.stalkIdeal_definingIdealOfHom_eq_ker g z]
    at ha
  obtain ⟨V, hz, s, hs, rfl⟩ := (Stacks.RingedSpace.mem_stalkIdeal_iff _).mp ha
  obtain ⟨x, hx⟩ := Stacks.Conormal.AffineCotangent.Sections.exists_section_of_app_eq_zero
    (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom g.toLRSHom.toShHom))
    (op V) s hs
  refine ⟨TopCat.Presheaf.germ (C := Ab.{u})
    (Stacks.ClosedImmersion.idealSheaf g.toLRSHom.toShHom).val.presheaf V (g.base z) hz x, ?_⟩
  exact (idealStalkHom_germ g (g.base z) V hz x).trans
    (congrArg (W.presheaf.germ V (g.base z) hz) hx)

/-- **The stalk of the ideal sheaf of an immersion is the kernel of the map of local rings.**
The identification sends the germ of a section to the germ of its image in `𝒪_W`. -/
private def idealStalkLinearEquiv [IsImmersion g] (z : Z) :
    ToType (TopCat.Presheaf.stalk (C := Ab.{u})
        (Stacks.ClosedImmersion.idealSheaf g.toLRSHom.toShHom).val.presheaf (g.base z))
      ≃ₗ[ToType (W.presheaf.stalk (g.base z))] RingHom.ker (g.stalkMap z).hom :=
  LinearEquiv.ofBijective
    { toFun := fun ξ => ⟨idealStalkHom g (g.base z) ξ, idealStalkHom_mem_ker g z ξ⟩
      map_add' := fun a b => Subtype.ext (map_add (idealStalkHom g (g.base z)) a b)
      map_smul' := fun r a => Subtype.ext (idealStalkHom_smul g (g.base z) r a) }
    ⟨fun ξ η h => idealStalkHom_injective g (g.base z) (congrArg Subtype.val h),
      fun b => by
        obtain ⟨ξ, hξ⟩ := exists_idealStalkHom_eq g z b.1 b.2
        exact ⟨ξ, Subtype.ext hξ⟩⟩

private theorem idealStalkLinearEquiv_germ [IsImmersion g] (z : Z) (V : W.Opens)
    (hz : g.base z ∈ V)
    (s : (Stacks.ClosedImmersion.idealSheaf g.toLRSHom.toShHom).val.obj (op V)) :
    idealStalkLinearEquiv g z (TopCat.Presheaf.germ (C := Ab.{u})
        (Stacks.ClosedImmersion.idealSheaf g.toLRSHom.toShHom).val.presheaf V (g.base z) hz s) =
      ⟨(W.presheaf.germ V (g.base z) hz) (idealSection g V s),
        germ_idealSection_mem_ker_stalkMap g z V hz s⟩ :=
  Subtype.ext (idealStalkHom_germ g (g.base z) V hz s)

end IdealStalk

/-! ### The stalk of the conormal sheaf -/

section Conormal

variable {Z X : Scheme.{u}} (j : Z ⟶ X) [IsImmersion j] (z : Z)

/-- The local ring of `Z` at `z` as an algebra over the local ring of the coborder
neighbourhood of the image of `j` at the image of `z`, through the stalk map of
`j.liftCoborder`. -/
abbrev stalkMapAlgebra :
    Algebra (ToType (j.coborderRange.toScheme.presheaf.stalk (j.liftCoborder.base z)))
      (ToType (Z.presheaf.stalk z)) :=
  (j.liftCoborder.stalkMap z).hom.toAlgebra

attribute [local instance] stalkMapAlgebra

/-- The cotangent module `I/I²` of the kernel `I` of the stalk map of `j.liftCoborder` at `z`,
as a module over the local ring of `Z` at `z`, through the identification of that local ring
with the quotient by `I`. -/
abbrev cotangentStalkModule :
    Module (ToType (Z.presheaf.stalk z))
      (RingHom.ker (j.liftCoborder.stalkMap z).hom).Cotangent :=
  Module.compHom (RingHom.ker (j.liftCoborder.stalkMap z).hom).Cotangent
    (RingHom.quotientKerEquivOfSurjective
      (j.liftCoborder.stalkMap_surjective z)).symm.toRingHom

attribute [local instance] cotangentStalkModule

/-- The stalk at `z` of the conormal sheaf of `j`, identified with the base change along the
map of local rings of the stalk of the ideal sheaf of `j.liftCoborder`. -/
private def conormalPullbackStalkEquiv :
    ToType (TopCat.Presheaf.stalk (C := Ab.{u}) (conormalSheaf j).val.presheaf z)
      ≃ₗ[ToType (Z.presheaf.stalk z)]
      TensorProduct (ToType (j.coborderRange.toScheme.presheaf.stalk (j.liftCoborder.base z)))
        (ToType (Z.presheaf.stalk z))
        (ToType (TopCat.Presheaf.stalk (C := Ab.{u})
          (Stacks.ClosedImmersion.idealSheaf j.liftCoborder.toLRSHom.toShHom).val.presheaf
            (j.liftCoborder.base z))) :=
  (exists_modulePullbackStalkLinearEquiv j.liftCoborder.toLRSHom.toShHom
    (Stacks.ClosedImmersion.idealSheaf j.liftCoborder.toLRSHom.toShHom) z).choose

private theorem conormalPullbackStalkEquiv_germ (V : (j.coborderRange.toScheme).Opens)
    (hz : j.liftCoborder.base z ∈ V)
    (s : (Stacks.ClosedImmersion.idealSheaf
      j.liftCoborder.toLRSHom.toShHom).val.obj (op V)) :
    conormalPullbackStalkEquiv j z
        (TopCat.Presheaf.germ (C := Ab.{u}) (conormalSheaf j).val.presheaf
          ((opensMap j.liftCoborder.toLRSHom.toShHom).obj V) z hz
          (((modulePullbackPushforwardAdjunction
              j.liftCoborder.toLRSHom.toShHom).unit.app
            (Stacks.ClosedImmersion.idealSheaf
              j.liftCoborder.toLRSHom.toShHom)).val.app (op V) s)) =
      (1 : ToType (Z.presheaf.stalk z)) ⊗ₜ TopCat.Presheaf.germ (C := Ab.{u})
        (Stacks.ClosedImmersion.idealSheaf j.liftCoborder.toLRSHom.toShHom).val.presheaf
        V (j.liftCoborder.base z) hz s :=
  (exists_modulePullbackStalkLinearEquiv j.liftCoborder.toLRSHom.toShHom
    (Stacks.ClosedImmersion.idealSheaf j.liftCoborder.toLRSHom.toShHom) z).choose_spec V hz s

/-- The stalk at `z` of the conormal sheaf of `j`, identified with the base change of the
kernel of the map of local rings. -/
private def conormalStalkTensorKerEquiv :
    ToType (TopCat.Presheaf.stalk (C := Ab.{u}) (conormalSheaf j).val.presheaf z)
      ≃ₗ[ToType (Z.presheaf.stalk z)]
      TensorProduct (ToType (j.coborderRange.toScheme.presheaf.stalk (j.liftCoborder.base z)))
        (ToType (Z.presheaf.stalk z))
        (RingHom.ker (j.liftCoborder.stalkMap z).hom) :=
  (conormalPullbackStalkEquiv j z).trans
    (TensorProduct.AlgebraTensorModule.congr
      (LinearEquiv.refl (ToType (Z.presheaf.stalk z)) (ToType (Z.presheaf.stalk z)))
      (idealStalkLinearEquiv j.liftCoborder z))

private theorem conormalStalkTensorKerEquiv_germ (V : (j.coborderRange.toScheme).Opens)
    (hz : j.liftCoborder.base z ∈ V)
    (s : (Stacks.ClosedImmersion.idealSheaf
      j.liftCoborder.toLRSHom.toShHom).val.obj (op V)) :
    conormalStalkTensorKerEquiv j z
        (TopCat.Presheaf.germ (C := Ab.{u}) (conormalSheaf j).val.presheaf
          ((opensMap j.liftCoborder.toLRSHom.toShHom).obj V) z hz
          (((modulePullbackPushforwardAdjunction
              j.liftCoborder.toLRSHom.toShHom).unit.app
            (Stacks.ClosedImmersion.idealSheaf
              j.liftCoborder.toLRSHom.toShHom)).val.app (op V) s)) =
      (1 : ToType (Z.presheaf.stalk z)) ⊗ₜ
        (⟨(j.coborderRange.toScheme.presheaf.germ V (j.liftCoborder.base z) hz)
            (idealSection j.liftCoborder V s),
          germ_idealSection_mem_ker_stalkMap j.liftCoborder z V hz s⟩ :
            RingHom.ker (j.liftCoborder.stalkMap z).hom) :=
  (congrArg (fun t => TensorProduct.AlgebraTensorModule.congr
      (LinearEquiv.refl (ToType (Z.presheaf.stalk z)) (ToType (Z.presheaf.stalk z)))
      (idealStalkLinearEquiv j.liftCoborder z) t)
    (conormalPullbackStalkEquiv_germ j z V hz s)).trans
    (congrArg (fun y : RingHom.ker (j.liftCoborder.stalkMap z).hom =>
        (1 : ToType (Z.presheaf.stalk z)) ⊗ₜ y)
      (idealStalkLinearEquiv_germ j.liftCoborder z V hz s))

/-- **The stalk of the conormal sheaf of an immersion is a cotangent module.** For an immersion
`j : Z ⟶ X` and `z : Z`, the stalk at `z` of the conormal sheaf of `j` is `I/I²`, where `I` is
the kernel of the surjection of local rings induced by the canonical closed immersion of `Z`
into the coborder neighbourhood of the image of `j`. -/
@[no_expose]
def conormalSheafStalkEquivCotangent :
    ToType (TopCat.Presheaf.stalk (C := Ab.{u}) (conormalSheaf j).val.presheaf z)
      ≃ₗ[ToType (Z.presheaf.stalk z)]
      (RingHom.ker (j.liftCoborder.stalkMap z).hom).Cotangent :=
  (conormalStalkTensorKerEquiv j z).trans
    (tensorKerEquivCotangent (j.liftCoborder.stalkMap z).hom
      (j.liftCoborder.stalkMap_surjective z))

/-- **The identification carries conormal classes to conormal classes.** The germ at `z` of the
conormal class of a section `s` of the ideal sheaf over an open neighbourhood of the image of
`z` goes to the class modulo `I²` of the germ of the image of `s` in the structure sheaf. -/
theorem conormalSheafStalkEquivCotangent_germ (V : (j.coborderRange.toScheme).Opens)
    (hz : j.liftCoborder.base z ∈ V)
    (s : (Stacks.ClosedImmersion.idealSheaf
      j.liftCoborder.toLRSHom.toShHom).val.obj (op V)) :
    conormalSheafStalkEquivCotangent j z
        (TopCat.Presheaf.germ (C := Ab.{u}) (conormalSheaf j).val.presheaf
          ((opensMap j.liftCoborder.toLRSHom.toShHom).obj V) z hz
          (((modulePullbackPushforwardAdjunction
              j.liftCoborder.toLRSHom.toShHom).unit.app
            (Stacks.ClosedImmersion.idealSheaf
              j.liftCoborder.toLRSHom.toShHom)).val.app (op V) s)) =
      (RingHom.ker (j.liftCoborder.stalkMap z).hom).toCotangent
        ⟨(j.coborderRange.toScheme.presheaf.germ V (j.liftCoborder.base z) hz)
            (idealSection j.liftCoborder V s),
          germ_idealSection_mem_ker_stalkMap j.liftCoborder z V hz s⟩ :=
  (congrArg (fun t => tensorKerEquivCotangent (j.liftCoborder.stalkMap z).hom
      (j.liftCoborder.stalkMap_surjective z) t)
    (conormalStalkTensorKerEquiv_germ j z V hz s)).trans
    (tensorKerEquivCotangent_one_tmul (j.liftCoborder.stalkMap z).hom
      (j.liftCoborder.stalkMap_surjective z) _)

end Conormal

end Stacks.Conormal

end
