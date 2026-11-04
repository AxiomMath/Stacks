module

public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
public import StacksFrontier.CategoryTheory.Abelian.SerreClass.Coreflective

/-!
# Kernels and images in a coreflective subcategory, through a weak Serre class

Let `D` be an abelian category, `i : C ⥤ D` a fully faithful functor out of a preadditive category
with a right adjoint `Q : D ⥤ C`, and `P` a weak Serre class of `D` (**Stacks 0754**) containing
the image of `i`, on which `Q` is right exact. This is the shape of the coherator
`Q : Mod(𝒪_𝒳) → QCoh(𝒪_𝒳)` of **Stacks 0778** with `P = LQCoh^fbc(𝒪_𝒳)` (**Stacks 0779**), and
the statements below are the formal content of **Stacks 0GQL**:

* `C` is abelian, by `CategoryTheory.DeltaFunctor.abelianOfCoreflectionOnClass`; the statements
  below do not depend on which abelian structure `C` carries;
* for `φ : X ⟶ Y` in `C`, the kernel of `i φ` computed in `D` lies in `P`, and `Q` of it, with its
  map to `X`, is a kernel of `φ` in `C`
  (`CategoryTheory.Abelian.isLimitCoreflectorKernelFork`);
* the image of `i φ` computed in `D` lies in `P`, and `Q` of it is an image of `φ` in `C`
  (`CategoryTheory.Abelian.coreflectorImageIsImage`): the epimorphism `i X ⟶ Im(i φ)` lies in `P`
  and `Q` carries it to a regular epimorphism, being right exact on `P`; the monomorphism
  `Im(i φ) ⟶ i Y` stays a monomorphism under the right adjoint `Q`; and a factorisation through a
  strong epimorphism followed by a monomorphism is an image.

## Main definitions

* `CategoryTheory.Abelian.coreflectorKernelι` and
  `CategoryTheory.Abelian.coreflectorImageMonoFactorisation`: the kernel map `Q(Ker(i φ)) ⟶ X`
  and the factorisation of `φ` through `Q(Im(i φ))`.

## Implementation notes

No abelian structure on `C` is used: the statements involve only limits in `D` and the universal
property of images, and the strong epimorphism is produced directly as a regular one.
-/

@[expose] public section

open CategoryTheory.Limits

universe vC uC vD uD

namespace CategoryTheory.Abelian

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  {i : C ⥤ D} {Q : D ⥤ C} (adj : i ⊣ Q) [i.Full] [i.Faithful]

/-! ### Kernels -/

/-- The map `Q(Ker(i φ)) ⟶ X`: `Q` of the inclusion of the kernel of `i φ` computed in `D`,
followed by the inverse of the unit of the adjunction, which is an isomorphism since `i` is fully
faithful. -/
noncomputable def coreflectorKernelι {X Y : C} (φ : X ⟶ Y) : Q.obj (kernel (i.map φ)) ⟶ X :=
  Q.map (kernel.ι (i.map φ)) ≫ inv (adj.unit.app X)

omit [Preadditive C] in
private theorem unit_comp_map {X' Y' : C} (φ' : X' ⟶ Y') :
    adj.unit.app X' ≫ Q.map (i.map φ') = φ' ≫ adj.unit.app Y' :=
  (adj.unit.naturality φ').symm

/-- The map `Q(Ker(i φ)) ⟶ X` composed with `φ` is zero. -/
theorem coreflectorKernelι_comp {X Y : C} (φ : X ⟶ Y) :
    coreflectorKernelι adj φ ≫ φ = 0 := by
  have h : inv (adj.unit.app X) ≫ φ = Q.map (i.map φ) ≫ inv (adj.unit.app Y) := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, unit_comp_map, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  have : Q.IsRightAdjoint := adj.isRightAdjoint
  rw [coreflectorKernelι, Category.assoc, h, ← Category.assoc, ← Q.map_comp, kernel.condition,
    Q.map_zero, zero_comp]

/-- **`Q(Ker(i φ))` is a kernel of `φ` in `C`.** The right adjoint `Q` preserves the kernel of
`i φ`, and `Q (i φ)` is `φ` up to the unit isomorphisms. -/
noncomputable def isLimitCoreflectorKernelFork {X Y : C} (φ : X ⟶ Y) :
    IsLimit (KernelFork.ofι (coreflectorKernelι adj φ) (coreflectorKernelι_comp adj φ)) := by
  have : Q.IsRightAdjoint := adj.isRightAdjoint
  have hQ := isLimitOfHasKernelOfPreservesLimit Q (i.map φ)
  have hz : ∀ {W : C} (g : W ⟶ X), g ≫ φ = 0 → (g ≫ adj.unit.app X) ≫ Q.map (i.map φ) = 0 :=
    fun g hg => by rw [Category.assoc, unit_comp_map, ← Category.assoc, hg, zero_comp]
  refine KernelFork.IsLimit.ofι _ _
    (fun g hg => (KernelFork.IsLimit.lift' hQ (g ≫ adj.unit.app X) (hz g hg)).1) ?_ ?_
  · intro W g hg
    have hl := (KernelFork.IsLimit.lift' hQ (g ≫ adj.unit.app X) (hz g hg)).2
    simp only [Fork.ι_ofι] at hl
    rw [coreflectorKernelι, ← Category.assoc, hl, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  · intro W g hg m hm
    refine Fork.IsLimit.hom_ext hQ ?_
    have hl := (KernelFork.IsLimit.lift' hQ (g ≫ adj.unit.app X) (hz g hg)).2
    simp only [Fork.ι_ofι] at hl ⊢
    rw [hl, ← hm, coreflectorKernelι, Category.assoc, Category.assoc, IsIso.inv_hom_id,
      Category.comp_id]

/-! ### The restriction to a weak Serre class -/

variable (P : ObjectProperty D) (hiP : ∀ X, P (i.obj X))

variable [P.IsWeakSerreClass] [PreservesFiniteColimits (P.ι ⋙ Q)]

include hiP in
/-- The kernel of `i φ` computed in `D` lies in the weak Serre class `P`. -/
theorem prop_kernel_map {X Y : C} (φ : X ⟶ Y) : P (kernel (i.map φ)) :=
  P.prop_kernel _ (hiP X) (hiP Y)

include hiP in
/-- The image of `i φ` computed in `D` lies in the weak Serre class `P`: it is the kernel of the
cokernel of `i φ`. -/
theorem prop_image_map {X Y : C} (φ : X ⟶ Y) : P (Abelian.image (i.map φ)) :=
  P.prop_kernel _ (hiP Y) (P.prop_cokernel _ (hiP X) (hiP Y))

/-! ### Images -/

/-- The factorisation of `φ` through `Q(Im(i φ))`: the unit followed by `Q` of the epimorphism
`i X ⟶ Im(i φ)`, then `Q` of the monomorphism `Im(i φ) ⟶ i Y` followed by the inverse unit. -/
noncomputable def coreflectorImageMonoFactorisation {X Y : C} (φ : X ⟶ Y) :
    MonoFactorisation φ where
  I := Q.obj (Abelian.image (i.map φ))
  m := Q.map (Abelian.image.ι (i.map φ)) ≫ inv (adj.unit.app Y)
  m_mono := by
    have : Q.IsRightAdjoint := adj.isRightAdjoint
    infer_instance
  e := adj.unit.app X ≫ Q.map (Abelian.factorThruImage (i.map φ))
  fac := by
    rw [Category.assoc, ← Category.assoc (Q.map _), ← Q.map_comp, Abelian.image.fac,
      ← Category.assoc, unit_comp_map, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

include adj hiP in
/-- `Q` of the projection `i X ⟶ Coim(i φ)` onto the coimage computed in `D` is a regular
epimorphism of `C`: the projection is the cokernel of `Ker(i φ) ⟶ i X`, a cokernel inside `P`,
and `Q` is right exact on `P`. -/
theorem isRegularEpi_map_coimage_π {X Y : C} (φ : X ⟶ Y) :
    IsRegularEpi (Q.map (Abelian.coimage.π (i.map φ))) := by
  have : Q.IsRightAdjoint := adj.isRightAdjoint
  let K : P.FullSubcategory := ⟨kernel (i.map φ), prop_kernel_map P hiP φ⟩
  let A : P.FullSubcategory := ⟨i.obj X, hiP X⟩
  let M : P.FullSubcategory :=
    ⟨Abelian.coimage (i.map φ), P.prop_cokernel _ (prop_kernel_map P hiP φ) (hiP X)⟩
  let k : K ⟶ A := ObjectProperty.homMk (kernel.ι (i.map φ))
  let π : A ⟶ M := ObjectProperty.homMk (Abelian.coimage.π (i.map φ))
  have w : k ≫ π = 0 := P.ι.map_injective (by
    rw [Functor.map_comp, Functor.map_zero]
    exact cokernel.condition (kernel.ι (i.map φ)))
  have hc : IsColimit (CokernelCofork.ofπ π w) :=
    isColimitOfReflects P.ι
      ((isColimitMapCoconeCoforkEquiv' P.ι w).symm (cokernelIsCokernel (kernel.ι (i.map φ))))
  have hQ := (isColimitMapCoconeCoforkEquiv' (P.ι ⋙ Q) w) (isColimitOfPreserves (P.ι ⋙ Q) hc)
  have hw : (P.ι ⋙ Q).map k ≫ (P.ι ⋙ Q).map π = 0 ≫ (P.ι ⋙ Q).map π := by
    rw [← Functor.map_comp, w, Functor.map_zero, zero_comp]
  exact ⟨⟨RegularEpi.mk ((P.ι ⋙ Q).obj K) ((P.ι ⋙ Q).map k) 0 hw hQ⟩⟩

include hiP in
/-- The first map of `CategoryTheory.Abelian.coreflectorImageMonoFactorisation` is a strong
epimorphism: up to isomorphisms it is `Q` of the projection onto the coimage, a regular
epimorphism. -/
theorem strongEpi_coreflectorImageMonoFactorisation_e {X Y : C} (φ : X ⟶ Y) :
    StrongEpi (coreflectorImageMonoFactorisation adj φ).e := by
  have := isRegularEpi_map_coimage_π adj P hiP φ
  have hfac : Abelian.factorThruImage (i.map φ) =
      Abelian.coimage.π (i.map φ) ≫ Abelian.coimageImageComparison (i.map φ) := by
    simp [Abelian.coimageImageComparison]
  show StrongEpi (adj.unit.app X ≫ Q.map (Abelian.factorThruImage (i.map φ)))
  rw [hfac, Q.map_comp]
  infer_instance

include hiP in
/-- **`Q(Im(i φ))` is an image of `φ` in `C`.** The factorisation
`CategoryTheory.Abelian.coreflectorImageMonoFactorisation` is a strong epimorphism followed by a
monomorphism. -/
noncomputable def coreflectorImageIsImage {X Y : C} (φ : X ⟶ Y) :
    IsImage (coreflectorImageMonoFactorisation adj φ) :=
  have := strongEpi_coreflectorImageMonoFactorisation_e adj P hiP φ
  StrongEpiMonoFactorisation.toMonoIsImage
    { toMonoFactorisation := coreflectorImageMonoFactorisation adj φ }

end CategoryTheory.Abelian

end
