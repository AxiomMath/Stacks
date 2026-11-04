module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.GradedObject

/-! # Graded objects in an abelian category form an abelian category

Stacks 0126: if `𝒜` is an abelian category, then the category `Gr(𝒜)` of graded objects of `𝒜`
is abelian. We prove this for `GradedObject β C` with an arbitrary index type `β` (the tag is
the case `β := ℤ`), by showing that the evaluation functors jointly create the structure:

* limits and colimits exist componentwise and are preserved by `GradedObject.eval`;
* the preadditive structure is componentwise;
* every mono/epi is componentwise, so it is the kernel of its cokernel/cokernel of its kernel
  because it is so in each degree.

This mirrors `Mathlib.Algebra.Homology.HomologicalComplexLimits` and
`Mathlib.Algebra.Homology.HomologicalComplexAbelian`, minus the differentials. We also record
the componentwise descriptions that make the instance usable: `kernelIsoApply`,
`cokernelIsoApply`, and exactness of a short complex of graded objects is componentwise
(`exact_iff_componentwise_exact`, `shortExact_iff_componentwise_shortExact`).
-/

@[expose] public section

open CategoryTheory Category Limits

namespace CategoryTheory.GradedObject

universe w v' u' v u

variable {β : Type w} {C : Type u} [Category.{v} C]

section Limits

variable {J : Type u'} [Category.{v'} J] (F : J ⥤ GradedObject β C)

/-- A cone of graded objects is limit if it is so in each degree. -/
def isLimitOfEval (s : Cone F) (hs : ∀ b, IsLimit ((eval b).mapCone s)) : IsLimit s where
  lift t b := (hs b).lift ((eval b).mapCone t)
  fac t j := funext fun b => (hs b).fac ((eval b).mapCone t) j
  uniq t m hm := funext fun b => (hs b).uniq ((eval b).mapCone t) (m b) fun j => congr($(hm j) b)

variable [∀ b, HasLimit (F ⋙ eval b)]

/-- A cone for a functor `F : J ⥤ GradedObject β C` given in each degree `b` by the limit
of `F ⋙ eval b`. -/
@[simps]
noncomputable def coneOfHasLimitEval : Cone F where
  pt b := limit (F ⋙ eval b)
  π :=
    { app := fun j b => limit.π (F ⋙ eval b) j
      naturality := fun _ _ φ => funext fun b => (id_comp _).trans (limit.w (F ⋙ eval b) φ).symm }

/-- The cone `coneOfHasLimitEval F` is limit. -/
noncomputable def isLimitConeOfHasLimitEval : IsLimit (coneOfHasLimitEval F) :=
  isLimitOfEval _ _ (fun _ => limit.isLimit _)

instance : HasLimit F := ⟨⟨⟨_, isLimitConeOfHasLimitEval F⟩⟩⟩

instance (b : β) : PreservesLimit F (eval b) :=
  preservesLimit_of_preserves_limit_cone (isLimitConeOfHasLimitEval F) (limit.isLimit _)

end Limits

section Colimits

variable {J : Type u'} [Category.{v'} J] (F : J ⥤ GradedObject β C)

/-- A cocone of graded objects is colimit if it is so in each degree. -/
def isColimitOfEval (s : Cocone F) (hs : ∀ b, IsColimit ((eval b).mapCocone s)) : IsColimit s where
  desc t b := (hs b).desc ((eval b).mapCocone t)
  fac t j := funext fun b => (hs b).fac ((eval b).mapCocone t) j
  uniq t m hm := funext fun b => (hs b).uniq ((eval b).mapCocone t) (m b) fun j => congr($(hm j) b)

variable [∀ b, HasColimit (F ⋙ eval b)]

/-- A cocone for a functor `F : J ⥤ GradedObject β C` given in each degree `b` by the colimit
of `F ⋙ eval b`. -/
@[simps]
noncomputable def coconeOfHasColimitEval : Cocone F where
  pt b := colimit (F ⋙ eval b)
  ι :=
    { app := fun j b => colimit.ι (F ⋙ eval b) j
      naturality := fun _ _ φ => funext fun b => (colimit.w (F ⋙ eval b) φ).trans (comp_id _).symm }

/-- The cocone `coconeOfHasColimitEval F` is colimit. -/
noncomputable def isColimitCoconeOfHasColimitEval : IsColimit (coconeOfHasColimitEval F) :=
  isColimitOfEval _ _ (fun _ => colimit.isColimit _)

instance : HasColimit F := ⟨⟨⟨_, isColimitCoconeOfHasColimitEval F⟩⟩⟩

instance (b : β) : PreservesColimit F (eval b) := preservesColimit_of_preserves_colimit_cocone
  (isColimitCoconeOfHasColimitEval F) (colimit.isColimit _)

end Colimits

section Shapes

variable {J : Type u'} [Category* J]

instance [HasLimitsOfShape J C] : HasLimitsOfShape J (GradedObject β C) := ⟨inferInstance⟩
instance [HasColimitsOfShape J C] : HasColimitsOfShape J (GradedObject β C) := ⟨inferInstance⟩
instance [HasFiniteLimits C] : HasFiniteLimits (GradedObject β C) := ⟨fun _ => inferInstance⟩
instance [HasFiniteColimits C] : HasFiniteColimits (GradedObject β C) := ⟨fun _ => inferInstance⟩

variable (b : β)

instance [HasLimitsOfShape J C] : PreservesLimitsOfShape J (eval (C := C) b) := ⟨inferInstance⟩
instance [HasColimitsOfShape J C] : PreservesColimitsOfShape J (eval (C := C) b) :=
  ⟨inferInstance⟩
instance [HasFiniteLimits C] : PreservesFiniteLimits (eval (C := C) b) := ⟨fun _ => inferInstance⟩
instance [HasFiniteColimits C] : PreservesFiniteColimits (eval (C := C) b) :=
  ⟨fun _ => inferInstance⟩

instance [HasFiniteLimits C] {X Y : GradedObject β C} (f : X ⟶ Y) [Mono f] (b : β) :
    Mono (f b) := inferInstanceAs (Mono ((eval b).map f))

instance [HasFiniteColimits C] {X Y : GradedObject β C} (f : X ⟶ Y) [Epi f] (b : β) :
    Epi (f b) := inferInstanceAs (Epi ((eval b).map f))

/-- A morphism of graded objects which is a monomorphism in each degree is a monomorphism. -/
lemma mono_of_mono_apply {X Y : GradedObject β C} (f : X ⟶ Y) (hf : ∀ b, Mono (f b)) : Mono f where
  right_cancellation g h eq := funext fun b => (hf b).right_cancellation (g b) (h b) congr($eq b)

/-- A morphism of graded objects which is an epimorphism in each degree is an epimorphism. -/
lemma epi_of_epi_apply {X Y : GradedObject β C} (f : X ⟶ Y) (hf : ∀ b, Epi (f b)) : Epi f where
  left_cancellation g h eq := funext fun b => (hf b).left_cancellation (g b) (h b) congr($eq b)

/-- A morphism of graded objects is a monomorphism iff it is so in each degree. -/
lemma mono_iff_mono_apply [HasFiniteLimits C] {X Y : GradedObject β C} (f : X ⟶ Y) :
    Mono f ↔ ∀ b, Mono (f b) := ⟨fun _ _ => inferInstance, mono_of_mono_apply f⟩

/-- A morphism of graded objects is an epimorphism iff it is so in each degree. -/
lemma epi_iff_epi_apply [HasFiniteColimits C] {X Y : GradedObject β C} (f : X ⟶ Y) :
    Epi f ↔ ∀ b, Epi (f b) := ⟨fun _ _ => inferInstance, epi_of_epi_apply f⟩

end Shapes

section ZeroMorphisms

variable [HasZeroMorphisms C]

instance eval_preservesZeroMorphisms (b : β) : (eval (C := C) b).PreservesZeroMorphisms where

/-- A graded object is zero iff it is so in each degree. -/
lemma isZero_iff (X : GradedObject β C) : IsZero X ↔ ∀ b, IsZero (X b) := by
  simp only [IsZero.iff_id_eq_zero]; exact ⟨fun h b ↦ congr($h b), funext⟩

end ZeroMorphisms

section Preadditive

variable [Preadditive C]

instance homAddCommGroup (X Y : GradedObject β C) : AddCommGroup (X ⟶ Y) where
  -- `zero` is spelled out so that it is *syntactically* the zero of the existing `Zero (X ⟶ Y)`
  -- instance; the two agree definitionally anyway (structure eta), but spelling it out follows
  -- `Preadditive.fullSubcategory`'s "transparency of definitional properties" convention.
  zero := 0
  __ := (inferInstanceAs (AddCommGroup (∀ b, X b ⟶ Y b)) : AddCommGroup (X ⟶ Y))

@[stacks 0126 "the preadditive structure, for an arbitrary index type"]
instance preadditive : Preadditive (GradedObject β C) where
  add_comp _ _ _ _ _ _ := funext fun _ => Preadditive.add_comp ..
  comp_add _ _ _ _ _ _ := funext fun _ => Preadditive.comp_add ..

variable {X Y : GradedObject β C}

@[simp] lemma add_apply (f g : X ⟶ Y) (b : β) : (f + g) b = f b + g b := rfl

@[simp] lemma neg_apply (f : X ⟶ Y) (b : β) : (-f) b = -f b := rfl

@[simp] lemma sub_apply (f g : X ⟶ Y) (b : β) : (f - g) b = f b - g b := rfl

instance eval_additive (b : β) : (eval (C := C) b).Additive where

end Preadditive

section Kernels

variable [HasZeroMorphisms C] [HasEqualizers C] {X Y : GradedObject β C}

/-- Kernels of morphisms of graded objects are computed degreewise. -/
noncomputable def kernelIsoApply (f : X ⟶ Y) (b : β) : kernel f b ≅ kernel (f b) :=
  PreservesKernel.iso (eval b) f

@[reassoc (attr := simp)]
lemma kernelIsoApply_hom_ι (f : X ⟶ Y) (b : β) :
    (kernelIsoApply f b).hom ≫ kernel.ι (f b) = kernel.ι f b := by
  simpa [kernelIsoApply] using kernelComparison_comp_ι f (eval b)

@[reassoc (attr := simp)]
lemma kernelIsoApply_inv_ι (f : X ⟶ Y) (b : β) :
    (kernelIsoApply f b).inv ≫ kernel.ι f b = kernel.ι (f b) := by simp [Iso.inv_comp_eq]

end Kernels

section Cokernels

variable [HasZeroMorphisms C] [HasCoequalizers C] {X Y : GradedObject β C}

/-- Cokernels of morphisms of graded objects are computed degreewise. -/
noncomputable def cokernelIsoApply (f : X ⟶ Y) (b : β) : cokernel f b ≅ cokernel (f b) :=
  PreservesCokernel.iso (eval b) f

@[reassoc (attr := simp)]
lemma π_cokernelIsoApply_inv (f : X ⟶ Y) (b : β) :
    cokernel.π (f b) ≫ (cokernelIsoApply f b).inv = cokernel.π f b := by
  simpa [cokernelIsoApply] using π_comp_cokernelComparison f (eval b)

@[reassoc (attr := simp)]
lemma π_cokernelIsoApply_hom (f : X ⟶ Y) (b : β) :
    cokernel.π f b ≫ (cokernelIsoApply f b).hom = cokernel.π (f b) := by simp [← Iso.eq_comp_inv]

end Cokernels

section Abelian

variable [Abelian C]

instance : IsNormalEpiCategory (GradedObject β C) := ⟨fun p _ =>
  ⟨NormalEpi.mk _ (kernel.ι p) (kernel.condition _)
    (isColimitOfEval _ _ (fun _ => Abelian.isColimitMapCoconeOfCokernelCoforkOfπ _ _))⟩⟩

instance : IsNormalMonoCategory (GradedObject β C) := ⟨fun i _ =>
  ⟨NormalMono.mk _ (cokernel.π i) (cokernel.condition _)
    (isLimitOfEval _ _ (fun _ => Abelian.isLimitMapConeOfKernelForkOfι _ _))⟩⟩

/-- **Stacks 0126**: the category of graded objects of an abelian category is abelian.
Stated for an arbitrary index type; the tag's statement is the case `β := ℤ`. -/
@[stacks 0126 "for an arbitrary index type"]
noncomputable instance abelian : Abelian (GradedObject β C) where

variable (S : ShortComplex (GradedObject β C))

/-- A short complex of graded objects is exact if it is so in each degree. -/
lemma exact_of_componentwise_exact (hS : ∀ b, (S.map (eval b)).Exact) : S.Exact := by
  simp only [ShortComplex.exact_iff_isZero_homology, isZero_iff] at hS ⊢
  exact fun b => .of_iso (hS b) (S.mapHomologyIso (eval b)).symm

/-- A short complex of graded objects is exact iff it is so in each degree. -/
lemma exact_iff_componentwise_exact : S.Exact ↔ ∀ b, (S.map (eval b)).Exact :=
  ⟨fun h b => h.map (eval b), exact_of_componentwise_exact S⟩

/-- A short complex of graded objects is short exact if it is so in each degree. -/
lemma shortExact_of_componentwise_shortExact (h : ∀ b, (S.map (eval b)).ShortExact) :
    S.ShortExact where
  mono_f := mono_of_mono_apply _ fun b => (h b).mono_f
  epi_g := epi_of_epi_apply _ fun b => (h b).epi_g
  exact := exact_of_componentwise_exact _ fun b => (h b).exact

/-- A short complex of graded objects is short exact iff it is so in each degree. -/
lemma shortExact_iff_componentwise_shortExact : S.ShortExact ↔ ∀ b, (S.map (eval b)).ShortExact :=
  ⟨fun h b => h.map_of_exact (eval b), shortExact_of_componentwise_shortExact S⟩

end Abelian

end CategoryTheory.GradedObject
