module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import StacksFrontier.Algebra.DirectSum.HomogeneousSubquotient
public import StacksFrontier.AlgebraicGeometry.ProjSheafFunctoriality.Basic

/-!
# Graded modules over a graded ring form an abelian category

`Stacks.AlgebraicGeometry.ProjSheafFunctoriality.GradedModuleCat 𝒮` is the category of
`ℤ`-graded modules over an `ℕ`-graded ring `S` and degree-preserving linear maps. This file
equips it with an abelian structure: the kernel of a degree-preserving map is the graded
submodule of homogeneous components killed by the map, and its cokernel is the quotient of the
target by the graded image.

## Main results

* `Stacks.AlgebraicGeometry.ProjSheafFunctoriality.GradedModuleCat.instAbelian`: the category
  of graded modules is abelian.
* `Stacks.AlgebraicGeometry.ProjSheafFunctoriality.GradedModuleCat.mono_iff_injective` and
  `Stacks.AlgebraicGeometry.ProjSheafFunctoriality.GradedModuleCat.epi_iff_surjective`: the
  monomorphisms and the epimorphisms are the degreewise maps which are injective, respectively
  surjective, on carriers.
* `Stacks.AlgebraicGeometry.ProjSheafFunctoriality.GradedModuleCat.exact_of_shortExact`: the
  underlying linear maps of a short exact sequence of graded modules are an exact sequence of
  modules.

## Implementation notes

The abelian structure is assembled in the order `Preadditive`, zero object, binary products,
kernels, cokernels, and then the two normality conditions, rather than through
`CategoryTheory.Abelian.ofCoimageImageComparisonIsIso`. Normality is the cheaper route here
because both normal factorizations are visible on carriers: a monomorphism is an injective map,
and the lift of a fork through it is degree-preserving because the preimage of a homogeneous
element of the image is homogeneous of the same degree, by injectivity.

The additive group of a hom-type is transferred from the additive subgroup of degree-preserving
maps inside all linear maps, so that each of the operations agrees with the corresponding
operation on `toLinearMap` definitionally.

The gradings of the kernel and the cokernel come from
`StacksFrontier/Algebra/DirectSum/HomogeneousSubquotient.lean`; what this file adds on the module
side is that `LinearMap.ker` and `LinearMap.range` of a degree-preserving map are homogeneous
submodules.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits DirectSum
open Stacks.GradedLocalization

namespace Stacks.AlgebraicGeometry.ProjSheafFunctoriality.GradedModuleCat

universe u v w

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  {𝒮 : ℕ → σ} [GradedRing 𝒮]

/-- The linear map underlying a composite is the composite of the underlying linear maps. -/
@[simp] public theorem comp_toLinearMap {M N P : GradedModuleCat.{u, v, w} 𝒮}
    (f : M ⟶ N) (g : N ⟶ P) :
    (f ≫ g).toLinearMap = g.toLinearMap.comp f.toLinearMap := rfl

/-- The linear map underlying the identity morphism is the identity. -/
@[simp] public theorem id_toLinearMap (M : GradedModuleCat.{u, v, w} 𝒮) :
    (𝟙 M : M ⟶ M).toLinearMap = LinearMap.id := rfl

/-- Two morphisms of graded modules with the same underlying linear map are equal. -/
public theorem hom_ext {M N : GradedModuleCat.{u, v, w} 𝒮} {f g : M ⟶ N}
    (h : f.toLinearMap = g.toLinearMap) : f = g := by
  obtain ⟨f, hf⟩ := f
  obtain ⟨g, hg⟩ := g
  dsimp only at h
  subst h
  rfl

/-! ### The preadditive structure -/

/-- The degree-preserving linear maps, as an additive subgroup of all linear maps. -/
public def homAddSubgroup (M N : GradedModuleCat.{u, v, w} 𝒮) :
    AddSubgroup (M.carrier →ₗ[S] N.carrier) where
  carrier := {f | ∀ (i : ℤ) (m : M.carrier), m ∈ M.grade i → f m ∈ N.grade i}
  zero_mem' _ _ _ := zero_mem _
  add_mem' hf hg i m hm := add_mem (hf i m hm) (hg i m hm)
  neg_mem' hf i m hm := neg_mem (hf i m hm)

/-- A degree-preserving morphism is the same thing as a degree-preserving linear map. -/
public def homEquiv (M N : GradedModuleCat.{u, v, w} 𝒮) :
    (M ⟶ N) ≃ homAddSubgroup M N where
  toFun f := ⟨f.toLinearMap, f.map_grade⟩
  invFun f := ⟨(f : M.carrier →ₗ[S] N.carrier), f.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The additive group of degree-preserving morphisms, with the operations of the underlying
linear maps. -/
public instance homAddCommGroup (M N : GradedModuleCat.{u, v, w} 𝒮) :
    AddCommGroup (M ⟶ N) := (homEquiv M N).addCommGroup

/-- The linear map underlying the zero morphism is zero. -/
@[simp] public theorem zero_toLinearMap (M N : GradedModuleCat.{u, v, w} 𝒮) :
    (0 : M ⟶ N).toLinearMap = 0 := rfl

/-- The linear map underlying a sum of morphisms is the sum of the underlying linear maps. -/
@[simp] public theorem add_toLinearMap {M N : GradedModuleCat.{u, v, w} 𝒮} (f g : M ⟶ N) :
    (f + g).toLinearMap = f.toLinearMap + g.toLinearMap := rfl

/-- The linear map underlying the negative of a morphism is the negative of its linear map. -/
@[simp] public theorem neg_toLinearMap {M N : GradedModuleCat.{u, v, w} 𝒮} (f : M ⟶ N) :
    (-f).toLinearMap = -f.toLinearMap := rfl

/-- The category of graded modules is preadditive. -/
public instance : Preadditive (GradedModuleCat.{u, v, w} 𝒮) where
  add_comp _ _ _ f f' g := hom_ext (by simp [LinearMap.comp_add])
  comp_add _ _ _ f g g' := hom_ext (by simp [LinearMap.add_comp])

/-! ### The zero object -/

/-- Every grading of a module with one element is a decomposition. -/
@[instance_reducible]
public def subsingletonDecomposition {A : Type*} [AddCommGroup A] [Subsingleton A]
    (𝒜 : ℤ → AddSubgroup A) : Decomposition 𝒜 where
  decompose' _ := 0
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := DirectSum.ext fun _ => Subtype.ext (Subsingleton.elim _ _)

/-- The zero graded module. -/
public def zeroObj : GradedModuleCat.{u, v, w} 𝒮 where
  carrier := PUnit.{v + 1}
  grade _ := ⊥
  decomposition := subsingletonDecomposition _
  gradedSMul := ⟨by intros; exact AddSubgroup.mem_bot.2 (Subsingleton.elim _ _)⟩

/-- The zero graded module is a zero object. -/
public theorem isZero_zeroObj : IsZero (zeroObj.{u, v, w} (𝒮 := 𝒮)) := by
  have hs : Subsingleton (zeroObj.{u, v, w} (𝒮 := 𝒮)).carrier :=
    inferInstanceAs (Subsingleton PUnit.{v + 1})
  constructor
  · intro Y
    refine ⟨⟨⟨0⟩, fun f => hom_ext (LinearMap.ext fun x => ?_)⟩⟩
    rw [show x = 0 from hs.elim _ _]
    simp
  · intro Y
    exact ⟨⟨⟨0⟩, fun f => hom_ext (LinearMap.ext fun _ => hs.elim _ _)⟩⟩

/-- The category of graded modules has a zero object. -/
public instance : HasZeroObject (GradedModuleCat.{u, v, w} 𝒮) :=
  ⟨⟨zeroObj, isZero_zeroObj⟩⟩

/-! ### Binary products -/

section Prod

variable (M N : GradedModuleCat.{u, v, w} 𝒮)

/-- The grading of the product of two graded modules. -/
public def prodGrade (i : ℤ) : AddSubgroup (M.carrier × N.carrier) :=
  (M.grade i).prod (N.grade i)

/-- Projection of a homogeneous piece of a product onto the first factor. -/
public def prodGradeFst (i : ℤ) : prodGrade M N i →+ M.grade i where
  toFun x := ⟨(x : M.carrier × N.carrier).1, x.2.1⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Projection of a homogeneous piece of a product onto the second factor. -/
public def prodGradeSnd (i : ℤ) : prodGrade M N i →+ N.grade i where
  toFun x := ⟨(x : M.carrier × N.carrier).2, x.2.2⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Inclusion of a homogeneous piece of the first factor into the product. -/
public def prodGradeInl (i : ℤ) : M.grade i →+ prodGrade M N i where
  toFun a := ⟨((a : M.carrier), 0), ⟨a.2, zero_mem _⟩⟩
  map_zero' := Subtype.ext (by simp)
  map_add' _ _ := Subtype.ext (by simp)

/-- Inclusion of a homogeneous piece of the second factor into the product. -/
public def prodGradeInr (i : ℤ) : N.grade i →+ prodGrade M N i where
  toFun b := ⟨(0, (b : N.carrier)), ⟨zero_mem _, b.2⟩⟩
  map_zero' := Subtype.ext (by simp)
  map_add' _ _ := Subtype.ext (by simp)

/-- Summing the homogeneous pieces of a product and projecting to the first factor agrees with
projecting each piece to the first factor and then summing. -/
public theorem fst_comp_coeAddMonoidHom_prodGrade :
    (AddMonoidHom.fst M.carrier N.carrier).comp
        (DirectSum.coeAddMonoidHom (prodGrade M N)) =
      (DirectSum.coeAddMonoidHom M.grade).comp (DirectSum.map (prodGradeFst M N)) :=
  DirectSum.addHom_ext fun i y => by simp [prodGradeFst]

/-- Summing the homogeneous pieces of a product and projecting to the second factor agrees with
projecting each piece to the second factor and then summing. -/
public theorem snd_comp_coeAddMonoidHom_prodGrade :
    (AddMonoidHom.snd M.carrier N.carrier).comp
        (DirectSum.coeAddMonoidHom (prodGrade M N)) =
      (DirectSum.coeAddMonoidHom N.grade).comp (DirectSum.map (prodGradeSnd M N)) :=
  DirectSum.addHom_ext fun i y => by simp [prodGradeSnd]

/-- Including the homogeneous pieces of the first factor into the product and summing agrees with
summing in the first factor and then including it into the product. -/
public theorem coeAddMonoidHom_prodGrade_comp_inl :
    (DirectSum.coeAddMonoidHom (prodGrade M N)).comp (DirectSum.map (prodGradeInl M N)) =
      (AddMonoidHom.inl M.carrier N.carrier).comp (DirectSum.coeAddMonoidHom M.grade) :=
  DirectSum.addHom_ext fun i y => by simp [prodGradeInl]

/-- Including the homogeneous pieces of the second factor into the product and summing agrees
with summing in the second factor and then including it into the product. -/
public theorem coeAddMonoidHom_prodGrade_comp_inr :
    (DirectSum.coeAddMonoidHom (prodGrade M N)).comp (DirectSum.map (prodGradeInr M N)) =
      (AddMonoidHom.inr M.carrier N.carrier).comp (DirectSum.coeAddMonoidHom N.grade) :=
  DirectSum.addHom_ext fun i y => by simp [prodGradeInr]

/-- An element of the direct sum of the homogeneous pieces of a product of graded modules is
determined by its sum. -/
private theorem injective_coeAddMonoidHom_prodGrade :
    Function.Injective (DirectSum.coeAddMonoidHom (prodGrade M N)) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro z hz
  have h₁ : DirectSum.coeAddMonoidHom M.grade (DirectSum.map (prodGradeFst M N) z) = 0 := by
    simpa [hz] using (DFunLike.congr_fun (fst_comp_coeAddMonoidHom_prodGrade M N) z).symm
  have h₂ : DirectSum.coeAddMonoidHom N.grade (DirectSum.map (prodGradeSnd M N) z) = 0 := by
    simpa [hz] using (DFunLike.congr_fun (snd_comp_coeAddMonoidHom_prodGrade M N) z).symm
  have e₁ : DirectSum.map (prodGradeFst M N) z = 0 :=
    (Decomposition.isInternal M.grade).1 (by simpa using h₁)
  have e₂ : DirectSum.map (prodGradeSnd M N) z = 0 :=
    (Decomposition.isInternal N.grade).1 (by simpa using h₂)
  refine DirectSum.ext fun i => Subtype.ext (Prod.ext ?_ ?_)
  · simpa [prodGradeFst] using congrArg (fun y => ((y i : M.grade i) : M.carrier)) e₁
  · simpa [prodGradeSnd] using congrArg (fun y => ((y i : N.grade i) : N.carrier)) e₂

/-- Every element of a product of graded modules is a sum of homogeneous elements of the
product grading. -/
private theorem surjective_coeAddMonoidHom_prodGrade :
    Function.Surjective (DirectSum.coeAddMonoidHom (prodGrade M N)) := by
  classical
  intro x
  refine ⟨DirectSum.map (prodGradeInl M N) (DirectSum.decompose M.grade x.1)
    + DirectSum.map (prodGradeInr M N) (DirectSum.decompose N.grade x.2), ?_⟩
  have hl := DFunLike.congr_fun (coeAddMonoidHom_prodGrade_comp_inl M N)
    (DirectSum.decompose M.grade x.1)
  have hr := DFunLike.congr_fun (coeAddMonoidHom_prodGrade_comp_inr M N)
    (DirectSum.decompose N.grade x.2)
  simp only [AddMonoidHom.coe_comp, Function.comp_apply] at hl hr
  rw [map_add, hl, hr]
  have hx₁ : DirectSum.coeAddMonoidHom M.grade (DirectSum.decompose M.grade x.1) = x.1 :=
    DirectSum.Decomposition.left_inv x.1
  have hx₂ : DirectSum.coeAddMonoidHom N.grade (DirectSum.decompose N.grade x.2) = x.2 :=
    DirectSum.Decomposition.left_inv x.2
  rw [hx₁, hx₂]
  simp

/-- The product of the gradings of two graded modules is an internal direct sum decomposition of
the product. -/
public theorem isInternal_prodGrade : DirectSum.IsInternal (prodGrade M N) :=
  ⟨injective_coeAddMonoidHom_prodGrade M N, surjective_coeAddMonoidHom_prodGrade M N⟩

/-- The product of two graded modules. -/
public def prodObj : GradedModuleCat.{u, v, w} 𝒮 where
  carrier := M.carrier × N.carrier
  grade := prodGrade M N
  decomposition := (isInternal_prodGrade M N).chooseDecomposition
  gradedSMul := ⟨by
    rintro i j a b ha hb
    exact ⟨SetLike.GradedSMul.smul_mem (A := 𝒮) (B := M.grade) ha hb.1,
      SetLike.GradedSMul.smul_mem (A := 𝒮) (B := N.grade) ha hb.2⟩⟩

/-- First projection out of the product of two graded modules. -/
public def prodFst : prodObj M N ⟶ M :=
  ⟨LinearMap.fst S M.carrier N.carrier, fun _ _ hm => hm.1⟩

/-- Second projection out of the product of two graded modules. -/
public def prodSnd : prodObj M N ⟶ N :=
  ⟨LinearMap.snd S M.carrier N.carrier, fun _ _ hm => hm.2⟩

/-- The product cone of two graded modules. -/
public def prodBinaryFan : BinaryFan M N := BinaryFan.mk (prodFst M N) (prodSnd M N)

/-- The product cone of two graded modules is a limit cone. -/
public def prodBinaryFanIsLimit : IsLimit (prodBinaryFan M N) :=
  BinaryFan.isLimitMk
    (fun s => ⟨LinearMap.prod (BinaryFan.fst s).toLinearMap (BinaryFan.snd s).toLinearMap,
      fun i m hm => ⟨(BinaryFan.fst s).map_grade i m hm, (BinaryFan.snd s).map_grade i m hm⟩⟩)
    (fun _ => hom_ext rfl) (fun _ => hom_ext rfl)
    (fun s _ h₁ h₂ => hom_ext (LinearMap.ext fun x => Prod.ext
      (congrArg (fun k : s.pt ⟶ M => k.toLinearMap x) h₁)
      (congrArg (fun k : s.pt ⟶ N => k.toLinearMap x) h₂)))

/-- Two graded modules have a binary product. -/
public instance : HasBinaryProduct M N :=
  ⟨⟨⟨prodBinaryFan M N, prodBinaryFanIsLimit M N⟩⟩⟩

end Prod

/-- The category of graded modules has binary products. -/
public instance : HasBinaryProducts (GradedModuleCat.{u, v, w} 𝒮) :=
  hasBinaryProducts_of_hasLimit_pair _

/-- The category of graded modules has finite products. -/
public instance : HasFiniteProducts (GradedModuleCat.{u, v, w} 𝒮) :=
  hasFiniteProducts_of_has_binary_and_terminal

/-! ### Monomorphisms and epimorphisms -/

/-- Equal morphisms of graded modules have equal underlying linear maps at every point. -/
private theorem toLinearMap_apply_congr {M N : GradedModuleCat.{u, v, w} 𝒮} {f g : M ⟶ N}
    (h : f = g) (x : M.carrier) : f.toLinearMap x = g.toLinearMap x := by
  rw [h]

/-- A morphism of graded modules whose underlying linear map is injective is a monomorphism. -/
public theorem mono_of_injective {M N : GradedModuleCat.{u, v, w} 𝒮} {f : M ⟶ N}
    (h : Function.Injective f.toLinearMap) : Mono f :=
  ⟨fun _ _ hgk => hom_ext (LinearMap.ext fun x =>
    h (toLinearMap_apply_congr hgk x))⟩

/-- A morphism of graded modules whose underlying linear map is surjective is an epimorphism. -/
public theorem epi_of_surjective {M N : GradedModuleCat.{u, v, w} 𝒮} {f : M ⟶ N}
    (h : Function.Surjective f.toLinearMap) : Epi f := by
  refine ⟨fun _ _ hgk => hom_ext (LinearMap.ext fun y => ?_)⟩
  obtain ⟨x, rfl⟩ := h y
  exact toLinearMap_apply_congr hgk x

/-! ### Kernels and cokernels -/

section KernelCokernel

variable {M N : GradedModuleCat.{u, v, w} 𝒮} (f : M ⟶ N)

/-- A degree-preserving map commutes with taking homogeneous components. -/
private theorem toLinearMap_decompose_apply (m : M.carrier) (i : ℤ) :
    f.toLinearMap (DirectSum.decompose M.grade m i : M.carrier) =
      (DirectSum.decompose N.grade (f.toLinearMap m) i : N.carrier) :=
  (Stacks.GradedModule.decompose_apply_map (ℳ := M.grade) (𝒩 := N.grade)
    f.toLinearMap.toAddMonoidHom (fun j x hx => f.map_grade j x hx) m i).symm

/-- The homogeneous components of an element killed by a degree-preserving map are killed by
it. -/
public theorem isHomogeneous_ker :
    SetLike.IsHomogeneous M.grade (LinearMap.ker f.toLinearMap) := by
  intro i m hm
  rw [LinearMap.mem_ker, toLinearMap_decompose_apply, LinearMap.mem_ker.1 hm]
  simp

/-- The homogeneous components of an element of the image of a degree-preserving map are again
in the image. -/
public theorem isHomogeneous_range :
    SetLike.IsHomogeneous N.grade (LinearMap.range f.toLinearMap) := by
  rintro i n ⟨m, rfl⟩
  exact ⟨_, toLinearMap_decompose_apply f m i⟩

/-- The kernel of a degree-preserving map, as a graded module. -/
public def kerObj : GradedModuleCat.{u, v, w} 𝒮 where
  carrier := LinearMap.ker f.toLinearMap
  grade := Stacks.GradedModule.subGrade M.grade (LinearMap.ker f.toLinearMap)
  decomposition := Stacks.GradedModule.subGradeDecomposition _ _ (isHomogeneous_ker f)
  gradedSMul := Stacks.GradedModule.subGrade_gradedSMul _ _ 𝒮

/-- The inclusion of the kernel of a degree-preserving map. -/
public def kerι : kerObj f ⟶ M :=
  ⟨(LinearMap.ker f.toLinearMap).subtype, fun _ _ hm => hm⟩

/-- The inclusion of the kernel composed with the map is zero. -/
public theorem kerι_comp : kerι f ≫ f = 0 :=
  hom_ext (LinearMap.ext fun x => x.2)

/-- The inclusion of the kernel is a monomorphism. -/
public instance : Mono (kerι f) := mono_of_injective fun _ _ hab => Subtype.ext hab

/-- The cokernel of a degree-preserving map, as a graded module. -/
public def cokerObj : GradedModuleCat.{u, v, w} 𝒮 where
  carrier := N.carrier ⧸ LinearMap.range f.toLinearMap
  grade := Stacks.GradedModule.quotGrade N.grade (LinearMap.range f.toLinearMap)
  decomposition := Stacks.GradedModule.quotGradeDecomposition _ _ (isHomogeneous_range f)
  gradedSMul := Stacks.GradedModule.quotGrade_gradedSMul _ _ 𝒮

/-- The projection onto the cokernel of a degree-preserving map. -/
public def cokerπ : N ⟶ cokerObj f :=
  ⟨(LinearMap.range f.toLinearMap).mkQ,
    fun _ _ hn => Stacks.GradedModule.mkQ_mem_quotGrade _ _ hn⟩

/-- The map composed with the projection onto its cokernel is zero. -/
public theorem comp_cokerπ : f ≫ cokerπ f = 0 :=
  hom_ext (LinearMap.ext fun x =>
    (Submodule.Quotient.mk_eq_zero _).2 (LinearMap.mem_range_self f.toLinearMap x))

/-- The projection onto the cokernel is an epimorphism. -/
public instance : Epi (cokerπ f) :=
  epi_of_surjective (Submodule.mkQ_surjective _)

/-- The kernel fork of a degree-preserving map is a limit cone. -/
public def kernelForkIsLimit : IsLimit (KernelFork.ofι (kerι f) (kerι_comp f)) :=
  KernelFork.IsLimit.ofι' _ _ fun {A} k hk =>
    ⟨⟨LinearMap.codRestrict (LinearMap.ker f.toLinearMap) k.toLinearMap fun x =>
        show (k ≫ f).toLinearMap x = 0 by rw [hk]; rfl,
      fun i m hm => k.map_grade i m hm⟩, hom_ext (LinearMap.ext fun _ => rfl)⟩

/-- The cokernel cofork of a degree-preserving map is a colimit cocone. -/
public def cokernelCoforkIsColimit :
    IsColimit (CokernelCofork.ofπ (cokerπ f) (comp_cokerπ f)) :=
  CokernelCofork.IsColimit.ofπ' _ _ fun {A} k hk =>
    ⟨⟨Submodule.liftQ _ k.toLinearMap (by
        rintro _ ⟨x, rfl⟩
        change (f ≫ k).toLinearMap x = 0
        rw [hk]
        rfl),
      fun i y hy => by
        obtain ⟨n, hn, rfl⟩ := (Stacks.GradedModule.mem_quotGrade _ _).1 hy
        exact k.map_grade i n hn⟩, hom_ext (LinearMap.ext fun _ => rfl)⟩

/-- A degree-preserving map has a kernel. -/
public instance : HasKernel f := ⟨⟨⟨_, kernelForkIsLimit f⟩⟩⟩

/-- A degree-preserving map has a cokernel. -/
public instance : HasCokernel f := ⟨⟨⟨_, cokernelCoforkIsColimit f⟩⟩⟩

end KernelCokernel

/-- The category of graded modules has kernels. -/
public instance : HasKernels (GradedModuleCat.{u, v, w} 𝒮) := ⟨fun _ => inferInstance⟩

/-- The category of graded modules has cokernels. -/
public instance : HasCokernels (GradedModuleCat.{u, v, w} 𝒮) := ⟨fun _ => inferInstance⟩

/-! ### Normality -/

section Normal

variable {M N : GradedModuleCat.{u, v, w} 𝒮} (f : M ⟶ N)

/-- A morphism of graded modules is a monomorphism if and only if its underlying linear map is
injective. -/
public theorem mono_iff_injective : Mono f ↔ Function.Injective f.toLinearMap := by
  refine ⟨fun _ => ?_, mono_of_injective⟩
  have h : kerι f = 0 := (cancel_mono f).1 (by simp [kerι_comp])
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  exact toLinearMap_apply_congr h ⟨x, hx⟩

/-- A morphism of graded modules is an epimorphism if and only if its underlying linear map is
surjective. -/
public theorem epi_iff_surjective : Epi f ↔ Function.Surjective f.toLinearMap := by
  refine ⟨fun _ n => ?_, epi_of_surjective⟩
  have h : cokerπ f = 0 := (cancel_epi f).1 (by simp [comp_cokerπ])
  have h₂ : (cokerπ f).toLinearMap n = 0 :=
    toLinearMap_apply_congr h n
  exact (Submodule.Quotient.mk_eq_zero _).1 h₂

/-- A monomorphism of graded modules is the kernel of its cokernel. -/
@[instance_reducible]
public def normalMono (hf : Mono f) : NormalMono f where
  Z := cokerObj f
  g := cokerπ f
  w := comp_cokerπ f
  isLimit := by
    have hinj : Function.Injective f.toLinearMap := (mono_iff_injective f).1 hf
    refine KernelFork.IsLimit.ofι' _ _ fun {A} k hk => ?_
    have hmem : ∀ x : A.carrier, k.toLinearMap x ∈ LinearMap.range f.toLinearMap := fun x =>
      (Submodule.Quotient.mk_eq_zero _).1 (show (k ≫ cokerπ f).toLinearMap x = 0 by rw [hk]; rfl)
    have hval : ∀ z : LinearMap.range f.toLinearMap,
        f.toLinearMap ((LinearEquiv.ofInjective f.toLinearMap hinj).symm z) = (z : N.carrier) :=
      fun z => congrArg Subtype.val
        ((LinearEquiv.ofInjective f.toLinearMap hinj).apply_symm_apply z)
    refine ⟨⟨(LinearEquiv.ofInjective f.toLinearMap hinj).symm.toLinearMap.comp
      (LinearMap.codRestrict (LinearMap.range f.toLinearMap) k.toLinearMap hmem), ?_⟩,
      hom_ext (LinearMap.ext fun x => hval ⟨k.toLinearMap x, hmem x⟩)⟩
    intro i x hx
    set y := (LinearEquiv.ofInjective f.toLinearMap hinj).symm ⟨k.toLinearMap x, hmem x⟩ with hy
    have hfy : f.toLinearMap y = k.toLinearMap x := hval ⟨k.toLinearMap x, hmem x⟩
    have hd := Stacks.GradedModule.decompose_apply_map (ℳ := M.grade) (𝒩 := N.grade)
      f.toLinearMap.toAddMonoidHom (fun j z hz => f.map_grade j z hz) y i
    have hcomp : f.toLinearMap ((DirectSum.decompose M.grade y i : M.carrier)) =
        f.toLinearMap y := by
      rw [show f.toLinearMap ((DirectSum.decompose M.grade y i : M.carrier)) =
          f.toLinearMap.toAddMonoidHom ((DirectSum.decompose M.grade y i : M.carrier)) from rfl,
        ← hd, show f.toLinearMap.toAddMonoidHom y = k.toLinearMap x from hfy, hfy]
      exact DirectSum.decompose_of_mem_same N.grade (k.map_grade i x hx)
    have hyi : (DirectSum.decompose M.grade y i : M.carrier) = y := hinj hcomp
    change y ∈ M.grade i
    exact hyi ▸ (DirectSum.decompose M.grade y i).2

/-- An epimorphism of graded modules is the cokernel of its kernel. -/
@[instance_reducible]
public def normalEpi (hf : Epi f) : NormalEpi f where
  W := kerObj f
  g := kerι f
  w := kerι_comp f
  isColimit := by
    have hsurj : Function.Surjective f.toLinearMap := (epi_iff_surjective f).1 hf
    refine CokernelCofork.IsColimit.ofπ' _ _ fun {A} k hk => ?_
    have hle : LinearMap.ker f.toLinearMap ≤ LinearMap.ker k.toLinearMap := fun x hx =>
      show (kerι f ≫ k).toLinearMap ⟨x, hx⟩ = 0 by rw [hk]; rfl
    have hmk : ∀ z : M.carrier,
        (LinearMap.quotKerEquivOfSurjective f.toLinearMap hsurj).symm (f.toLinearMap z) =
          Submodule.Quotient.mk z :=
      fun z => (LinearEquiv.symm_apply_eq _).2
        (by simp [LinearMap.quotKerEquivOfSurjective])
    refine ⟨⟨(Submodule.liftQ _ k.toLinearMap hle).comp
      (LinearMap.quotKerEquivOfSurjective f.toLinearMap hsurj).symm.toLinearMap, ?_⟩, ?_⟩
    · intro i n hn
      obtain ⟨x, hx⟩ := hsurj n
      have hd := Stacks.GradedModule.decompose_apply_map (ℳ := M.grade) (𝒩 := N.grade)
        f.toLinearMap.toAddMonoidHom (fun j z hz => f.map_grade j z hz) x i
      have hxi : f.toLinearMap ((DirectSum.decompose M.grade x i : M.carrier)) = n := by
        rw [show f.toLinearMap ((DirectSum.decompose M.grade x i : M.carrier)) =
            f.toLinearMap.toAddMonoidHom ((DirectSum.decompose M.grade x i : M.carrier)) from rfl,
          ← hd, show f.toLinearMap.toAddMonoidHom x = n from hx]
        exact DirectSum.decompose_of_mem_same N.grade hn
      change (Submodule.liftQ _ k.toLinearMap hle)
        ((LinearMap.quotKerEquivOfSurjective f.toLinearMap hsurj).symm n) ∈ A.grade i
      rw [← hxi, hmk ((DirectSum.decompose M.grade x i : M.carrier))]
      exact k.map_grade i _ (DirectSum.decompose M.grade x i).2
    · refine hom_ext (LinearMap.ext fun z => ?_)
      change (Submodule.liftQ _ k.toLinearMap hle)
        ((LinearMap.quotKerEquivOfSurjective f.toLinearMap hsurj).symm
          (f.toLinearMap z)) = k.toLinearMap z
      rw [hmk z]
      rfl

end Normal

/-- Every monomorphism of graded modules is normal. -/
public instance : IsNormalMonoCategory (GradedModuleCat.{u, v, w} 𝒮) where
  normalMonoOfMono f hf := ⟨normalMono f hf⟩

/-- Every epimorphism of graded modules is normal. -/
public instance : IsNormalEpiCategory (GradedModuleCat.{u, v, w} 𝒮) where
  normalEpiOfEpi f hf := ⟨normalEpi f hf⟩

/-- **Graded modules over a graded ring form an abelian category.** -/
public instance instAbelian : Abelian (GradedModuleCat.{u, v, w} 𝒮) where

/-! ### Short exact sequences read on carriers -/

/-- A zero graded module has only one element. -/
public theorem subsingleton_of_isZero {M : GradedModuleCat.{u, v, w} 𝒮} (h : IsZero M) :
    Subsingleton M.carrier := by
  have hid : (𝟙 M : M ⟶ M) = 0 := h.eq_of_tgt _ _
  refine ⟨fun x y => ?_⟩
  exact (toLinearMap_apply_congr hid x).trans (toLinearMap_apply_congr hid y).symm

/-- In a short exact sequence of graded modules, every element of the middle term killed by the
second map comes from the first. -/
public theorem exists_preimage_of_shortExact {T : ShortComplex (GradedModuleCat.{u, v, w} 𝒮)}
    (hT : T.ShortExact) (y : T.X₂.carrier) (hy : T.g.toLinearMap y = 0) :
    ∃ x, T.f.toLinearMap x = y := by
  obtain ⟨l, hl⟩ := KernelFork.IsLimit.lift' hT.fIsKernel (kerι T.g) (kerι_comp T.g)
  exact ⟨l.toLinearMap ⟨y, hy⟩,
    toLinearMap_apply_congr hl ⟨y, hy⟩⟩

/-- The underlying linear maps of a short exact sequence of graded modules form an exact
sequence of modules. -/
public theorem exact_of_shortExact {T : ShortComplex (GradedModuleCat.{u, v, w} 𝒮)}
    (hT : T.ShortExact) : Function.Exact T.f.toLinearMap T.g.toLinearMap := by
  intro y
  refine ⟨fun hy => exists_preimage_of_shortExact hT y hy, ?_⟩
  rintro ⟨x, rfl⟩
  exact toLinearMap_apply_congr T.zero x

end Stacks.AlgebraicGeometry.ProjSheafFunctoriality.GradedModuleCat

end
