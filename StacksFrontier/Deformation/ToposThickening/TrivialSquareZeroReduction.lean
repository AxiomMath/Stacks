module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.SqZeroExtAnySite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsEpiFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheaf
public import StacksFrontier.Deformation.ToposThickening.SquareZeroLiftTorsor

/-!
# The trivial square-zero extension of a sheaf of rings and its reduction triangle

Let `O₀` be a sheaf of commutative rings on a site and `M` a sheaf of `O₀`-modules. The trivial
square-zero extension `O₀[M] = O₀ ⊕ M`, with `(a, m) (a', m') = (a a', a m' + a' m)`, is again
a sheaf of commutative rings, and its projection `O₀[M] ⟶ O₀` is a surjection whose kernel `M`
has square zero. So it is a square-zero thickening in the sense of Stacks 0DIY and 0DIZ, and
its ideal is `M` *by construction*: the inclusion `M ⟶ O₀[M]`, `m ↦ (0, m)`, identifies `M`,
read as an `O₀[M]`-module through the projection, with the kernel of the projection.

This is the ring sheaf of the proof of Stacks 0DLL. There `X_V = X₀ ×_{Spec k} Spec(k[V])` for
a finite-dimensional `k`-vector space `V`, and on the small étale site of `X₀` its structure
sheaf is `O₀[O₀ ⊗_k V]`; a linear map `V ⟶ W` induces the map `O₀[V] ⟶ O₀[W]` over `O₀`,
`Deformation.ComplexLift.sqZeroExtSheafAnySiteMap`.

The site is the one of the small étale site of an algebraic space: objects in `Type (u + 1)`,
morphisms and sections in `Type u`. The small-site construction
`Stacks.Sheaves.Differentials.sqZeroExtSheaf` does not apply there, which is why this file
carries the `AnySite` marker of `PresheafOfModules.sqZeroExtPresheafAnySite`.

Nothing here is registered.

## Main definitions

* `Deformation.ComplexLift.sqZeroExtSheafAnySite`: the sheaf of commutative rings `O₀[M]`.
* `Deformation.ComplexLift.sqZeroExtSheafAnySiteProj`: the projection `O₀[M] ⟶ O₀`.
* `Deformation.ComplexLift.sqZeroExtSheafAnySiteMap`: the map `O₀[M] ⟶ O₀[N]` induced by a
  morphism `M ⟶ N` of `O₀`-modules.
* `Deformation.ComplexLift.sqZeroExtIdealInclusion`: the inclusion `M ⟶ O₀[M]` of the ideal, as a
  morphism of `O₀[M]`-modules.
* `Deformation.ComplexLift.sqZeroExtReduction`: the reduction triangle
  `K ⊗^L M ⟶ K ⟶ K ⊗^L O₀ ⟶ (K ⊗^L M)⟦1⟧` of the projection, computed by flat resolutions.

## Main results

* `Deformation.ComplexLift.isLocallySurjective_sqZeroExtSheafAnySiteProj` and
  `Deformation.ComplexLift.sqZeroExtSheafAnySiteProj_mul_eq_zero`: the projection is a
  surjection with square-zero kernel, the hypotheses `hf` and `hsq` of Stacks 0DIZ.
* `Deformation.ComplexLift.shortExact_sqZeroExtIdealSequence`: `0 ⟶ M ⟶ O₀[M] ⟶ O₀ ⟶ 0` is short
  exact.

## References

* [Stacks Project, Tag 0DLL](https://stacks.math.columbia.edu/tag/0DLL)
* [Stacks Project, Tag 0DIZ](https://stacks.math.columbia.edu/tag/0DIZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe d d₀ u

namespace Deformation.ComplexLift

open PresheafOfModules

variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

section Ring

variable (O₀ : Sheaf J CommRingCat.{u})

/-- The square-zero extension of a sheaf of commutative rings by a sheaf of modules satisfies the
sheaf condition: on underlying types it is the product of the two sheaves of types. -/
theorem isSheaf_sqZeroExtPresheafAnySite
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)) :
    Presheaf.IsSheaf J (sqZeroExtPresheafAnySite (R := O₀.obj) M.val) := by
  refine Stacks.Sites.isSheaf_commRingCat_of_isSheaf_forget J _ ?_
  rw [← isSheaf_iff_isSheaf_of_type]
  refine Stacks.NoncommChangeOfRings.Silver.isSheaf_of_bijective_pair
    (P := (Stacks.SheafOfModules.Tensor.ringSheaf O₀).obj ⋙ forget RingCat.{u})
    (Q := M.val.presheaf ⋙ forget AddCommGrpCat.{u})
    (Stacks.NoncommChangeOfRings.Silver.isSheaf_forget_of_isSheaf _
      (Stacks.SheafOfModules.Tensor.ringSheaf O₀).property)
    ((isSheaf_iff_isSheaf_of_type _ _).2 ((isSheaf_iff_isSheaf_of_type _ _).1
      (Presheaf.isSheaf_comp_of_isSheaf _ _ _ (SheafOfModules.isSheaf M))))
    (fun _ x => sqZeroExtFstAnySite (M := M.val) x) (fun _ x => sqZeroExtSndAnySite (M := M.val) x)
    (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => ⟨fun x y h => ?_, fun p => ⟨sqZeroExtMkAnySite (M := M.val) (U := _) p.1 p.2, rfl⟩⟩)
  exact sqZeroExt_ext_anySite (congrArg Prod.fst h) (congrArg Prod.snd h)

/-- **The trivial square-zero extension `O₀[M] = O₀ ⊕ M`** of a sheaf of commutative rings by a
sheaf of `O₀`-modules, with multiplication `(a, m) (a', m') = (a a', a m' + a' m)`. -/
def sqZeroExtSheafAnySite (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)) :
    Sheaf J CommRingCat.{u} where
  obj := sqZeroExtPresheafAnySite (R := O₀.obj) M.val
  property := isSheaf_sqZeroExtPresheafAnySite O₀ M

variable {O₀}

/-- The projection `O₀[M] ⟶ O₀`, `(a, m) ↦ a`. -/
def sqZeroExtSheafAnySiteProj
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)) :
    sqZeroExtSheafAnySite O₀ M ⟶ O₀ :=
  ObjectProperty.homMk
    { app _ := CommRingCat.ofHom
        { toFun := fun x => sqZeroExtFstAnySite (M := M.val) x
          map_one' := rfl
          map_mul' := fun _ _ => rfl
          map_zero' := rfl
          map_add' := fun _ _ => rfl }
      naturality _ _ _ := rfl }

/-- On sections, the projection `O₀[M] ⟶ O₀` sends `x` to its first component. -/
@[simp]
theorem sqZeroExtSheafAnySiteProj_app
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)) (U : Cᵒᵖ)
    (x : (sqZeroExtSheafAnySite O₀ M).obj.obj U) :
    (sqZeroExtSheafAnySiteProj M).hom.app U x = sqZeroExtFstAnySite (M := M.val) x := rfl

/-- **The projection of the trivial square-zero extension is surjective**, sectionwise and so
locally. -/
theorem isLocallySurjective_sqZeroExtSheafAnySiteProj
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)) :
    Presheaf.IsLocallySurjective J (sqZeroExtSheafAnySiteProj M).hom :=
  Presheaf.isLocallySurjective_of_surjective J _ fun U a =>
    ⟨sqZeroExtMkAnySite (M := M.val) (U := U) a 0, rfl⟩

/-- **The kernel of the projection has square zero.** -/
theorem sqZeroExtSheafAnySiteProj_mul_eq_zero
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)) (U : Cᵒᵖ)
    (a b : (sqZeroExtSheafAnySite O₀ M).obj.obj U)
    (ha : (sqZeroExtSheafAnySiteProj M).hom.app U a = 0)
    (hb : (sqZeroExtSheafAnySiteProj M).hom.app U b = 0) : a * b = 0 := by
  have ha' : sqZeroExtFstAnySite (M := M.val) a = 0 := ha
  have hb' : sqZeroExtFstAnySite (M := M.val) b = 0 := hb
  refine sqZeroExt_ext_anySite ?_ ?_
  · show sqZeroExtFstAnySite (M := M.val) a * sqZeroExtFstAnySite (M := M.val) b = 0
    rw [ha', zero_mul]
  · show sqZeroExtFstAnySite (M := M.val) a • sqZeroExtSndAnySite (M := M.val) b +
      sqZeroExtFstAnySite (M := M.val) b • sqZeroExtSndAnySite (M := M.val) a = 0
    simp [ha', hb']

/-- **The map `O₀[M] ⟶ O₀[N]` induced by a morphism `φ : M ⟶ N` of `O₀`-modules**,
`(a, m) ↦ (a, φ m)`. -/
def sqZeroExtSheafAnySiteMap
    {M N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)} (φ : M ⟶ N) :
    sqZeroExtSheafAnySite O₀ M ⟶ sqZeroExtSheafAnySite O₀ N :=
  ObjectProperty.homMk
    { app U := CommRingCat.ofHom
        { toFun := fun x => sqZeroExtMkAnySite (M := N.val)
            (sqZeroExtFstAnySite (M := M.val) x) (φ.val.app U (sqZeroExtSndAnySite (M := M.val) x))
          map_one' := sqZeroExt_ext_anySite rfl (map_zero _)
          map_mul' := fun x y => sqZeroExt_ext_anySite rfl (by
            change φ.val.app U (sqZeroExtFstAnySite (M := M.val) x • sqZeroExtSndAnySite y +
                sqZeroExtFstAnySite (M := M.val) y • sqZeroExtSndAnySite x) =
              sqZeroExtFstAnySite (M := M.val) x • φ.val.app U (sqZeroExtSndAnySite y) +
                sqZeroExtFstAnySite (M := M.val) y • φ.val.app U (sqZeroExtSndAnySite x)
            rw [map_add]
            exact congrArg₂ (· + ·) ((φ.val.app U).hom.map_smul _ _)
              ((φ.val.app U).hom.map_smul _ _))
          map_zero' := sqZeroExt_ext_anySite rfl (map_zero _)
          map_add' := fun x y => sqZeroExt_ext_anySite rfl (map_add _ _ _) }
      naturality {U V} i := by
        ext x
        refine sqZeroExt_ext_anySite rfl ?_
        change φ.val.app V (M.val.map i (sqZeroExtSndAnySite (M := M.val) x)) =
          N.val.map i (φ.val.app U (sqZeroExtSndAnySite (M := M.val) x))
        exact PresheafOfModules.naturality_apply φ.val i (sqZeroExtSndAnySite (M := M.val) x) }

/-- The map `O₀[M] ⟶ O₀[N]` induced by `φ : M ⟶ N` commutes with the projections to `O₀`. -/
@[simp]
theorem sqZeroExtSheafAnySiteMap_comp_proj
    {M N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)} (φ : M ⟶ N) :
    sqZeroExtSheafAnySiteMap φ ≫ sqZeroExtSheafAnySiteProj N = sqZeroExtSheafAnySiteProj M :=
  rfl

/-- The section `O₀ ⟶ O₀[M]`, `a ↦ (a, 0)`, of the projection. -/
def sqZeroExtSheafAnySiteSection
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)) :
    O₀ ⟶ sqZeroExtSheafAnySite O₀ M :=
  ObjectProperty.homMk (PresheafOfModules.sqZeroExtInlAnySite (R := O₀.obj) M.val)

/-- **The section is a section of the projection.** -/
@[simp]
theorem sqZeroExtSheafAnySiteSection_comp_proj
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)) :
    sqZeroExtSheafAnySiteSection M ≫ sqZeroExtSheafAnySiteProj M = 𝟙 O₀ :=
  rfl

end Ring

section Ideal

variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O₀ : Sheaf J CommRingCat.{u}}
  (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))

/-- **The inclusion `M ⟶ O₀[M]` of the ideal**, `m ↦ (0, m)`, as a morphism of sheaves of
`O₀[M]`-modules, `M` being read as an `O₀[M]`-module through the projection. -/
def sqZeroExtIdealInclusion :
    restrictIdeal (sqZeroExtSheafAnySiteProj M) M ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (sqZeroExtSheafAnySite O₀ M)) :=
  ⟨PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom (AddMonoidHom.mk'
        (fun m => sqZeroExtMkAnySite (M := M.val) (U := U) 0 m)
        (fun m n => sqZeroExt_ext_anySite (add_zero 0).symm rfl))
      naturality {U V} i := by
        ext m
        exact sqZeroExt_ext_anySite (M := M.val) (map_zero (O₀.obj.map i).hom).symm rfl }
    (fun U r m => sqZeroExt_ext_anySite (mul_zero _).symm (by
      change sqZeroExtFstAnySite (M := M.val) (U := U) r • (show M.val.obj U from m) =
        sqZeroExtFstAnySite (M := M.val) (U := U) r • (show M.val.obj U from m) +
          (0 : O₀.obj.obj U) • sqZeroExtSndAnySite (M := M.val) (U := U) r
      rw [zero_smul, add_zero]))⟩

omit [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat] in
/-- On sections, the ideal inclusion `M ⟶ O₀[M]` sends `m` to `(0, m)`. -/
@[simp]
theorem sqZeroExtIdealInclusion_val_app (U : Cᵒᵖ) (m : M.val.obj U) :
    (sqZeroExtIdealInclusion M).val.app U m = sqZeroExtMkAnySite (M := M.val) (U := U) 0 m :=
  rfl

omit [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat] in
/-- The map `O₀[M] ⟶ O₀[N]` induced by `φ : M ⟶ N` carries the ideal inclusion of `M` to the ideal
inclusion of `N` precomposed with `φ`, section by section. -/
theorem sqZeroExtSheafAnySiteMap_idealInclusion {N : SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf O₀)} (φ : M ⟶ N) (U : Cᵒᵖ) (m : M.val.obj U) :
    (sqZeroExtSheafAnySiteMap φ).hom.app U ((sqZeroExtIdealInclusion M).val.app U m) =
      (sqZeroExtIdealInclusion N).val.app U (φ.val.app U m) :=
  sqZeroExt_ext_anySite rfl rfl

/-- The ideal inclusion `M ⟶ O₀[M]` composed with the map `O₀[M] ⟶ O₀` induced by the projection
is zero. -/
theorem sqZeroExtIdealInclusion_comp :
    sqZeroExtIdealInclusion M ≫ structureModuleMap (sqZeroExtSheafAnySiteProj M) = 0 := by
  ext U m
  exact structureModuleMap_val_app (sqZeroExtSheafAnySiteProj M) U _

/-- The ideal `M` is the kernel of the projection `O₀[M] ⟶ O₀`, as sheaves of
`O₀[M]`-modules. -/
def sqZeroExtIdealKernelIso :
    restrictIdeal (sqZeroExtSheafAnySiteProj M) M ≅ kernelModule (sqZeroExtSheafAnySiteProj M) where
  hom := SheafOfModules.kerLift (sqZeroExtIdealInclusion M) (sqZeroExtIdealInclusion_comp M)
  inv := ⟨PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom (AddMonoidHom.mk'
        (fun x => sqZeroExtSndAnySite (M := M.val) (U := U) x.1) (fun _ _ => rfl))
      naturality {U V} i := by
        ext x
        rfl }
    (fun U r x => by
      have hx : sqZeroExtFstAnySite (M := M.val) (U := U) x.1 = 0 :=
        (structureModuleMap_val_app (sqZeroExtSheafAnySiteProj M) U x.1).symm.trans x.2
      change sqZeroExtFstAnySite (M := M.val) r • sqZeroExtSndAnySite (M := M.val) x.1 +
        sqZeroExtFstAnySite (M := M.val) x.1 • sqZeroExtSndAnySite r = _
      rw [hx, zero_smul, add_zero]
      rfl)⟩
  hom_inv_id := by
    ext U m
    rfl
  inv_hom_id := by
    ext U x
    have hx : sqZeroExtFstAnySite (M := M.val) (U := U) x.1 = 0 :=
      (structureModuleMap_val_app (sqZeroExtSheafAnySiteProj M) U x.1).symm.trans x.2
    exact Subtype.ext (sqZeroExt_ext_anySite hx.symm rfl)

/-- The isomorphism `M ≅ ker(O₀[M] ⟶ O₀)` composed with the kernel inclusion is the ideal
inclusion `M ⟶ O₀[M]`. -/
theorem sqZeroExtIdealKernelIso_hom_comp :
    (sqZeroExtIdealKernelIso M).hom ≫ SheafOfModules.kerIota
      (structureModuleMap (sqZeroExtSheafAnySiteProj M)) = sqZeroExtIdealInclusion M :=
  SheafOfModules.kerLift_comp _ (sqZeroExtIdealInclusion_comp M)

/-- **The ideal sequence `0 ⟶ M ⟶ O₀[M] ⟶ O₀ ⟶ 0` of the trivial square-zero extension is short
exact.** -/
theorem shortExact_sqZeroExtIdealSequence :
    (idealSequenceOf (sqZeroExtSheafAnySiteProj M) M (sqZeroExtIdealInclusion M)
      (sqZeroExtIdealInclusion_comp M)).ShortExact := by
  have := epi_structureModuleMap (sqZeroExtSheafAnySiteProj M)
    (isLocallySurjective_sqZeroExtSheafAnySiteProj M)
  have hK : (ShortComplex.mk (SheafOfModules.kerIota
      (structureModuleMap (sqZeroExtSheafAnySiteProj M)))
      (structureModuleMap (sqZeroExtSheafAnySiteProj M))
      (SheafOfModules.kerIota_comp _)).ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel _ (SheafOfModules.kerIsLimit _) }
  refine ShortComplex.shortExact_of_iso ?_ hK
  exact ShortComplex.isoMk (sqZeroExtIdealKernelIso M).symm (Iso.refl _) (Iso.refl _)
    (by
      dsimp
      rw [Category.comp_id, Iso.inv_comp_eq, sqZeroExtIdealKernelIso_hom_comp])
    (by simp)

variable [HasDerivedCategory.{d} (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (sqZeroExtSheafAnySite O₀ M)))]
  [HasDerivedCategory.{d₀} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))]

/-- **The reduction triangle of the trivial square-zero extension**: for `K ∈ D(O₀[M])`, the
triangle `(K ⊗^L O₀ ⊗^L M)|_{O₀[M]} ⟶ K ⟶ (K ⊗^L O₀)|_{O₀[M]} ⟶ …⟦1⟧` of the ideal sequence
`0 ⟶ M ⟶ O₀[M] ⟶ O₀ ⟶ 0`, computed by flat resolutions. Its ideal part is `- ⊗^L M` on the nose,
no identification of the kernel being needed. -/
def sqZeroExtReduction :
    DerivedReduction (derivedExtensionOfScalarsData.{d, d₀} (sqZeroExtSheafAnySiteProj M))
      (derivedTensorRight.{d₀} M) :=
  flatReduction.{d, d₀} (sqZeroExtSheafAnySiteProj M) (sqZeroExtIdealInclusion M)
    (sqZeroExtIdealInclusion_comp M) (shortExact_sqZeroExtIdealSequence M)

end Ideal

end Deformation.ComplexLift

end
