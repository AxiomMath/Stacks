module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentSite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafFlatCover
public import StacksCore.Tactic.StacksAttribute

/-!
# Tensoring a finitely presented sheaf of modules with a coherent one

Stacks 01CE: on a ringed space, the tensor product of a sheaf of modules of finite
presentation with a coherent sheaf of modules is coherent. The proof in the source is local:
over an open `U` on which `F` has a finite presentation
`𝒪_U^{⊕ ι} → 𝒪_U^{⊕ σ} → F|_U → 0`, right exactness of the tensor product presents
`(F ⊗ G)|_U` as the cokernel of a map `G|_U^{⊕ ι} → G|_U^{⊕ σ}`, and coherence then follows
from the closure properties of Stacks 01BY.

`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentSite` supplies those closure properties
over an arbitrary site, and `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafFlatCover`
supplies right exactness of the tensor product. What was missing, and is built here, is the
step that moves between the two: **the tensor product of sheaves of modules commutes with
restriction to a slice site**, so that a presentation of `F|_U` may be tensored *on the slice
site over `U`* and the answer recognized as the restriction of `F ⊗ G`.

The tensor product used is `Stacks.SheafOfModules.Tensor.sheafTensor`, "forget to presheaves of
modules, take the objectwise tensor product `Stacks.tensorObj`, sheafify", tensored on the right
by a fixed factor as `(sheafTensor O).flip.obj G`; see the implementation notes for the relation
to the other spellings of the tensor product of sheaves of modules on this branch.

## Main definitions

* `Stacks.TensorCoherence.overWhisker` is a morphism of presheaves on a site, restricted along
  `Over.forget U` to the slice site over `U`.
* `Stacks.TensorCoherence.presheafOver` is the restriction of presheaves of modules to the
  slice site over `U`, and `Stacks.TensorCoherence.tensorOverPresheafIso` identifies the
  objectwise tensor product of two restrictions with the restriction of the objectwise tensor
  product; on sections it is the identity.
* `Stacks.TensorCoherence.tensorOverUnit` is the sheafification unit of the objectwise tensor
  product, restricted to the slice site, and `Stacks.TensorCoherence.tensorSheafOverHom` the
  morphism adjoint to it.
* `Stacks.TensorCoherence.tensorObjMonoidalIso` identifies `Stacks.tensorObj` with Mathlib's
  monoidal product of presheaves of modules, and `Stacks.TensorCoherence.tensorObjUnitIso`,
  `Stacks.TensorCoherence.tensorSheafUnitIso` are the resulting left unit constraints for the
  objectwise tensor product and for the tensor product of sheaves of modules.

## Main results

* `Stacks.TensorCoherence.isLocallyInjective_overWhisker'` and
  `isLocallySurjective_overWhisker'`: **local injectivity and local surjectivity of a morphism
  of presheaves restrict to a slice site.** A sieve of `Over U` is covering for `J.over U`
  exactly when its image under `Over.forget U` is covering for `J`, and the equalizer sieve,
  respectively image sieve, of a section over `Z : Over U` for the restricted morphism is the
  preimage of the corresponding sieve over `Z.left`.
* `Stacks.TensorCoherence.isIso_sheafificationHomEquiv_symm`: **a locally bijective morphism
  from a presheaf of modules into a sheaf of modules exhibits the latter as the sheafification
  of the former.**
* `Stacks.TensorCoherence.tensorSheafOverIso`: **the tensor product of sheaves of modules
  commutes with restriction to a slice site**, `(F ⊗ G)|_U ≅ F|_U ⊗ G|_U`. This is the
  comparison that the previous two results produce: the objectwise tensor product commutes with
  restriction on the nose, and the restricted sheafification unit is still locally bijective, so
  it exhibits `(F ⊗ G)|_U` as the sheafification of the objectwise tensor product of the
  restrictions.
* `Stacks.TensorCoherence.isCoherent_tensor_free`: tensoring a finite free sheaf of modules with
  a coherent sheaf of modules gives a coherent sheaf of modules.
* `Stacks.TensorCoherence.isCoherent_tensor_of_presentation`: **the tensor product of a sheaf of
  modules with a global finite presentation and a coherent sheaf of modules is coherent, over an
  arbitrary site.** This is the mathematical content of Stacks 01CE, and also of Stacks 03L6,
  which is the same statement over a ringed site.
* `Stacks.TensorCoherence.isCoherent_tensorSheaf`: **Stacks Project, Tag 01CE.** The two
  previous results combined with `Stacks.SheafOfModules.Site.isCoherent_opens_of_coversTop`: a
  sheaf of modules of finite presentation has a finite presentation over each member of some
  open covering, the result above applies on the corresponding slice site, and
  `tensorSheafOverIso` transports the conclusion to a statement about `(F ⊗ G)|_U`.

## Implementation notes

**Which tensor product.** Stacks 01CE is stated in this library for three mutually isomorphic
but distinct constructions: `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf`,
`Stacks.SheafOfModules.TensorSheafification.tensorSheaf` and
`Stacks.SheafOfModules.Tensor.sheafTensor`. This file uses the last. The reason is
not taste: right exactness of the tensor product of sheaves of modules is already proved in
this library only for the right-handed `(sheafTensor O).flip.obj G`
(`Stacks.preservesColimitsOfSize_sheafTensorRight`), and that is one of the two inputs to the
argument. The two other constructions sheafify a presheaf whose sections over `U` are the same
tensor product `F(U) ⊗_{𝒪(U)} G(U)` with the same restriction maps on pure tensors, so each is
isomorphic to this one by the objectwise identity, in the shape in which
`tensorObjMonoidalIso` below writes that isomorphism for Mathlib's monoidal product. Those two
comparisons are not stated here because `Stacks.SheafOfModules.TensorStalkRingedSpace` carries a
  forty-module import list with
no business in a foundation module.

**Why the module universe equals the ring universe.** `Stacks.tensorObj` keeps the two module
universes independent of each other and of the ring universe, and so do the restriction results
of the first two sections. From `tensorObjUnitIso` onwards they must coincide: the left unit
constraint is taken from Mathlib's monoidal structure on presheaves of modules, which is
declared only for `PresheafOfModules.{u} (R ⋙ forget₂ _ _)` with `R : Cᵒᵖ ⥤ CommRingCat.{u}`,
and `SheafOfModules.IsFiniteType` — hence coherence — is likewise declared in Mathlib only for
`SheafOfModules.{u} R` with `R : Sheaf J RingCat.{u}`. Decoupling either is a change to
Mathlib. The site universes `u` and `v` stay independent throughout.

**`HasSheafCompose` is assumed rather than derived.** `Stacks.commRingSheafToRingSheaf`, the
sheaf of rings underlying a sheaf of commutative rings, is `sheafCompose J (forget₂ _ _)`
applied to it, so every statement about `Stacks.SheafOfModules.Tensor.sheafTensor` carries
`J.HasSheafCompose (forget₂ CommRingCat RingCat)`; the slice-site statements carry it for each
`J.over U` as well. On the site of opens of a topological space these are true but are not
found by instance search within the default heartbeat budget, which is why the space-level
section assumes them as instance arguments instead of discharging them.

**The explicit-hypothesis variants.** `isLocallyInjective_overWhisker'`,
`isLocallySurjective_overWhisker'`, `isLocallyInjective_of_fac`, `isLocallySurjective_of_fac`
and `isCoherent_of_iso'` take as explicit arguments what their instance-argument forms take by
synthesis. Two separate reasons force this. The universe parameters of
`Stacks.SheafOfModules.Site.IsCoherent` precede its instance arguments, so an application whose
expected type is not yet known has them defaulted to `0`; and the objects through which the
restricted sheafification unit factors agree only up to unfolding `PresheafOfModules.pushforward`,
which instance search, running at reducible transparency, will not do.

## References

* [Stacks Project, Tag 01CE](https://stacks.math.columbia.edu/tag/01CE)
* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
* [Stacks Project, Tag 03EX](https://stacks.math.columbia.edu/tag/03EX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe t v u w

namespace Stacks.TensorCoherence

section Restriction

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {D : Type*} [Category D] {FD : D → D → Type*} {CD : D → Type t}
  [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory.{t} D FD]
  {F₁ F₂ : Cᵒᵖ ⥤ D} (φ : F₁ ⟶ F₂) (U : C)

/-- The restriction of `φ` to the slice site over `U`. -/
abbrev overWhisker : (Over.forget U).op ⋙ F₁ ⟶ (Over.forget U).op ⋙ F₂ :=
  Functor.whiskerLeft (Over.forget U).op φ

/-- **Local injectivity restricts to a slice site.** The equalizer sieve of two sections of
`F₁` over `Z : Over U` is the preimage under `Over.forget U` of the equalizer sieve of the same
two sections of `F₁` over `Z.left`, and a sieve of the slice site is covering exactly when its
image under `Over.forget U` is. -/
theorem isLocallyInjective_overWhisker' (h : Presheaf.IsLocallyInjective J φ) :
    Presheaf.IsLocallyInjective (J.over U) (overWhisker φ U) where
  equalizerSieve_mem {Z} x y hxy :=
    J.overEquiv_symm_mem_over Z.unop (Presheaf.equalizerSieve (F := F₁) x y)
      (h.equalizerSieve_mem x y hxy)

/-- **Local surjectivity restricts to a slice site.** -/
theorem isLocallySurjective_overWhisker' (h : Presheaf.IsLocallySurjective J φ) :
    Presheaf.IsLocallySurjective (J.over U) (overWhisker φ U) where
  imageSieve_mem {Z} s :=
    J.overEquiv_symm_mem_over Z (Presheaf.imageSieve φ s) (h.imageSieve_mem s)

instance isLocallyInjective_overWhisker [Presheaf.IsLocallyInjective J φ] :
    Presheaf.IsLocallyInjective (J.over U) (overWhisker φ U) :=
  isLocallyInjective_overWhisker' J φ U inferInstance

instance isLocallySurjective_overWhisker [Presheaf.IsLocallySurjective J φ] :
    Presheaf.IsLocallySurjective (J.over U) (overWhisker φ U) :=
  isLocallySurjective_overWhisker' J φ U inferInstance

/-- Local injectivity of a composite, with the factorization supplied explicitly. -/
theorem isLocallyInjective_of_fac {F₃ : Cᵒᵖ ⥤ D} {ψ : F₂ ⟶ F₃} {φψ : F₁ ⟶ F₃}
    (fac : φ ≫ ψ = φψ) (hφ : Presheaf.IsLocallyInjective J φ)
    (hψ : Presheaf.IsLocallyInjective J ψ) : Presheaf.IsLocallyInjective J φψ := by
  subst fac
  have := hφ
  have := hψ
  infer_instance

/-- Local surjectivity of a composite, with the factorization supplied explicitly. -/
theorem isLocallySurjective_of_fac {F₃ : Cᵒᵖ ⥤ D} {ψ : F₂ ⟶ F₃} {φψ : F₁ ⟶ F₃}
    (fac : φ ≫ ψ = φψ) (hφ : Presheaf.IsLocallySurjective J φ)
    (hψ : Presheaf.IsLocallySurjective J ψ) : Presheaf.IsLocallySurjective J φψ := by
  subst fac
  have := hφ
  have := hψ
  infer_instance

end Restriction

section Uniqueness

/-- For an adjunction whose counit is an isomorphism, the morphism adjoint to `g` is an
isomorphism as soon as the image of `g` under the left adjoint is. -/
theorem isIso_homEquiv_symm {D : Type*} [Category D] {E : Type*} [Category E]
    {L : D ⥤ E} {G : E ⥤ D} (adj : L ⊣ G) [IsIso adj.counit] {X : D} {Y : E}
    (g : X ⟶ G.obj Y) (hg : IsIso (L.map g)) : IsIso ((adj.homEquiv X Y).symm g) := by
  have := hg
  rw [Adjunction.homEquiv_counit]
  infer_instance

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{w}} {R : Sheaf J RingCat.{w}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

/-- A locally bijective morphism from a presheaf of modules into (the restriction of scalars of)
a sheaf of modules exhibits the latter as the sheafification of the former. -/
theorem isIso_sheafificationHomEquiv_symm {P : PresheafOfModules.{w} R₀}
    {T : SheafOfModules.{w} R}
    (u : P ⟶ (SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars α).obj T)
    (hinj : Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf R₀).map u))
    (hsurj : Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf R₀).map u)) :
    IsIso ((PresheafOfModules.sheafificationHomEquiv α).symm u) := by
  have := hinj
  have := hsurj
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf.{w} R),
    PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm]
  have h : IsIso ((presheafToSheaf J AddCommGrpCat.{w}).map
      ((PresheafOfModules.toPresheaf R₀).map u)) :=
    (J.W_iff _).1 (J.W_of_isLocallyBijective _)
  exact isIso_homEquiv_symm _ _ h

end Uniqueness

section TensorOver

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {O : Sheaf J CommRingCat.{w}}

/-- The restriction of presheaves of modules to the slice site over `U`. -/
noncomputable abbrev presheafOver (U : C) :
    PresheafOfModules.{w} (Stacks.ringPresheaf O.obj) ⥤
      PresheafOfModules.{w} (Stacks.ringPresheaf ((Over.forget U).op ⋙ O.obj)) :=
  PresheafOfModules.pushforward (F := Over.forget U)
    (𝟙 (Stacks.ringPresheaf ((Over.forget U).op ⋙ O.obj)))

lemma toPresheaf_map_presheafOver_map (U : C)
    {P Q : PresheafOfModules.{w} (Stacks.ringPresheaf O.obj)} (f : P ⟶ Q) :
    (PresheafOfModules.toPresheaf _).map ((presheafOver U).map f) =
      overWhisker ((PresheafOfModules.toPresheaf _).map f) U := rfl

/-- The comparison identifying the objectwise tensor product of the restrictions to the slice
site over `U` with the restriction of the objectwise tensor product. On sections it is the
identity. -/
noncomputable def tensorOverPresheafIso (U : C)
    (P Q : PresheafOfModules.{w} (Stacks.ringPresheaf O.obj)) :
    Stacks.tensorObj ((presheafOver U).obj P) ((presheafOver U).obj Q) ≅
      (presheafOver U).obj (Stacks.tensorObj P Q) :=
  PresheafOfModules.isoMk (fun _ => Iso.refl _) (by intros; rfl)

variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [∀ U : C, (J.over U).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
  (F G : SheafOfModules.{w} (Stacks.commRingSheafToRingSheaf O))

/-- The morphism of presheaves of modules adjoint to `tensorSheafOverHom`: the sheafification
unit of the objectwise tensor product, restricted to the slice site over `U`. -/
noncomputable def tensorOverUnit (U : C) :
    Stacks.tensorObj ((presheafOver U).obj F.val) ((presheafOver U).obj G.val) ⟶
      (SheafOfModules.forget (Stacks.commRingSheafToRingSheaf (O.over U)) ⋙
          PresheafOfModules.restrictScalars
            (𝟙 (Stacks.commRingSheafToRingSheaf (O.over U)).obj)).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj G).obj
          F).over U) :=
  (tensorOverPresheafIso U F.val G.val).hom ≫
    (presheafOver U).map ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (Stacks.commRingSheafToRingSheaf O).obj)).unit.app (Stacks.tensorObj F.val G.val))

/-- **The tensor product of sheaves of modules commutes with restriction to a slice site.**
The comparison morphism, adjoint to the restricted sheafification unit. -/
noncomputable def tensorSheafOverHom (U : C) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{max u v, v, w, w, w} (O.over U)).flip.obj
        (G.over U)).obj (F.over U) ⟶
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj G).obj F).over U :=
  (PresheafOfModules.sheafificationHomEquiv
    (𝟙 (Stacks.commRingSheafToRingSheaf (O.over U)).obj)).symm (tensorOverUnit F G U)

omit [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}] in
/-- The factorization of the restricted sheafification unit through the comparison of the two
objectwise tensor products. -/
lemma toPresheaf_map_tensorOverUnit (U : C) :
    (PresheafOfModules.toPresheaf (Stacks.ringPresheaf ((Over.forget U).op ⋙ O.obj))).map
        (tensorOverPresheafIso U F.val G.val).hom ≫
      overWhisker ((PresheafOfModules.toPresheaf (Stacks.commRingSheafToRingSheaf O).obj).map
        ((PresheafOfModules.sheafificationAdjunction
          (𝟙 (Stacks.commRingSheafToRingSheaf O).obj)).unit.app
            (Stacks.tensorObj F.val G.val))) U =
      (PresheafOfModules.toPresheaf _).map (tensorOverUnit F G U) := rfl

instance isIso_tensorSheafOverHom (U : C) : IsIso (tensorSheafOverHom F G U) := by
  have h₁ : Presheaf.IsLocallyInjective (J.over U)
      ((PresheafOfModules.toPresheaf (Stacks.ringPresheaf ((Over.forget U).op ⋙ O.obj))).map
        (tensorOverPresheafIso U F.val G.val).hom) := inferInstance
  have h₂ : Presheaf.IsLocallySurjective (J.over U)
      ((PresheafOfModules.toPresheaf (Stacks.ringPresheaf ((Over.forget U).op ⋙ O.obj))).map
        (tensorOverPresheafIso U F.val G.val).hom) := inferInstance
  exact isIso_sheafificationHomEquiv_symm
    (α := 𝟙 (Stacks.commRingSheafToRingSheaf (O.over U)).obj) _
    (isLocallyInjective_of_fac (J.over U) _ (toPresheaf_map_tensorOverUnit F G U) h₁
      (isLocallyInjective_overWhisker' J _ U
        (PresheafOfModules.isLocallyInjective_sheafificationAdjunction_unit_app
          (𝟙 (Stacks.commRingSheafToRingSheaf O).obj) (Stacks.tensorObj F.val G.val))))
    (isLocallySurjective_of_fac (J.over U) _ (toPresheaf_map_tensorOverUnit F G U) h₂
      (isLocallySurjective_overWhisker' J _ U
        (PresheafOfModules.isLocallySurjective_sheafificationAdjunction_unit_app
          (𝟙 (Stacks.commRingSheafToRingSheaf O).obj) (Stacks.tensorObj F.val G.val))))

/-- **The tensor product of sheaves of modules commutes with restriction to a slice site.** -/
noncomputable def tensorSheafOverIso (U : C) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{max u v, v, w, w, w} (O.over U)).flip.obj
        (G.over U)).obj (F.over U) ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj G).obj F).over U :=
  asIso (tensorSheafOverHom F G U)

end TensorOver

section Unitor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {O : Sheaf J CommRingCat.{w}}

/-- **Mathlib's monoidal product of presheaves of modules is the objectwise tensor product
`Stacks.tensorObj`.** On sections both are the tensor product of the modules of sections, and
both restriction maps send a pure tensor to the tensor of the restrictions, so the comparison
is the identity on sections. -/
noncomputable def tensorObjMonoidalIso
    (P Q : PresheafOfModules.{w} (Stacks.ringPresheaf O.obj)) :
    Stacks.tensorObj P Q ≅ MonoidalCategory.tensorObj P Q :=
  PresheafOfModules.isoMk (fun _ => Iso.refl _) (by
    intro X Y f
    refine ModuleCat.hom_ext (TensorProduct.ext (by ext x y; rfl)))

/-- **The unit of the objectwise tensor product.** -/
noncomputable def tensorObjUnitIso (Q : PresheafOfModules.{w} (Stacks.ringPresheaf O.obj)) :
    Stacks.tensorObj (PresheafOfModules.unit (Stacks.ringPresheaf O.obj)) Q ≅ Q :=
  tensorObjMonoidalIso _ Q ≪≫ MonoidalCategory.leftUnitor Q

variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

/-- **The unit of the tensor product of sheaves of modules:** `𝒪 ⊗ G ≅ G`. -/
noncomputable def tensorSheafUnitIso
    (G : SheafOfModules.{w} (Stacks.commRingSheafToRingSheaf O)) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj G)).obj
        (SheafOfModules.unit (Stacks.commRingSheafToRingSheaf O)) ≅ G :=
  (Stacks.moduleSheafification O).mapIso (tensorObjUnitIso G.val) ≪≫ Stacks.sheafifyValIso O G

end Unitor

section Coherence

open Stacks.SheafOfModules.Site

variable {C : Type u} [Category.{v} C] [HasFiniteWidePullbacks C] [HasBinaryProducts C]
  [HasPullbacks C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {O : Sheaf J CommRingCat.{w}}
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ Y : C, HasSheafify (J.over Y) AddCommGrpCat.{w}]
  [∀ Y : C, (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ (Y : C) (Z : Over Y), HasSheafify ((J.over Y).over Z) AddCommGrpCat.{w}]
  [∀ (Y : C) (Z : Over Y), ((J.over Y).over Z).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ (Y : C) (Z : Over Y) (W : Over Z),
    HasSheafify (((J.over Y).over Z).over W) AddCommGrpCat.{w}]
  [∀ (Y : C) (Z : Over Y) (W : Over Z),
    (((J.over Y).over Z).over W).WEqualsLocallyBijective AddCommGrpCat.{w}]
  (G : SheafOfModules.{w} (Stacks.commRingSheafToRingSheaf O))

omit [HasPullbacks C] [HasSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ (Y : C) (Z : Over Y) (W : Over Z),
    HasSheafify (((J.over Y).over Z).over W) AddCommGrpCat.{w}]
  [∀ (Y : C) (Z : Over Y) (W : Over Z),
    (((J.over Y).over Z).over W).WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- Coherence transported along an isomorphism, with the hypothesis supplied explicitly: the
universe parameters of `IsCoherent` precede its instance arguments, so an application whose
expected type is not yet known defaults them to `0`. -/
theorem isCoherent_of_iso'
    {M N : SheafOfModules.{w} (Stacks.commRingSheafToRingSheaf O)} (e : M ≅ N)
    (hM : IsCoherent M) : IsCoherent N := by
  have := hM
  exact isCoherent_of_iso e

/-- **Tensoring a finite free sheaf of modules with a coherent sheaf of modules gives a
coherent sheaf of modules.** The tensor product commutes with the coproduct defining `free I`,
and `𝒪 ⊗ G ≅ G`, so the result is a finite direct sum of copies of `G`. -/
theorem isCoherent_tensor_free (hG : IsCoherent G) (I : Type w) [Finite I] :
    IsCoherent (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj G).obj
      (SheafOfModules.free I)) := by
  have : HasColimitsOfShape (Discrete I)
      (PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O).obj) :=
    PresheafOfModules.hasColimitsOfShape _ _
  have : HasColimitsOfShape (Discrete I)
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :=
    SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf _ _
  have hpc : PreservesColimitsOfSize.{w, w}
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj G) :=
    Stacks.preservesColimitsOfSize_sheafTensorRight O G
  have h : IsCoherent (∐ fun _ : I =>
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj G).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O))) :=
    isCoherent_sigma _ fun _ => isCoherent_of_iso' (tensorSheafUnitIso G).symm hG
  exact isCoherent_of_iso' (Limits.PreservesCoproduct.iso
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj G)
    (fun _ : I => SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O))).symm h

/-- **Stacks 01CE and 03L6, for a global finite presentation.** If a sheaf of modules `F` on a
site has a finite presentation by global sections and `G` is coherent, then `F ⊗ G` is
coherent: tensoring with `G` is right exact, so it carries the presentation of `F` to a
presentation of `F ⊗ G` by finite direct sums of copies of `G`, and coherent sheaves of modules
are closed under finite direct sums and cokernels. -/
theorem isCoherent_tensor_of_presentation
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) (hG : IsCoherent G)
    (P : F.Presentation) (hP : P.IsFinite) :
    IsCoherent
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj G).obj F) := by
  have := hP
  have hι : Finite P.relations.I := SheafOfModules.GeneratingSections.IsFiniteType.finite
  have hσ : Finite P.generators.I := SheafOfModules.GeneratingSections.IsFiniteType.finite
  have hpc : PreservesColimitsOfSize.{w, w}
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj G) :=
    Stacks.preservesColimitsOfSize_sheafTensorRight O G
  have hpc₀ : PreservesColimitsOfSize.{0, 0}
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj G) :=
    preservesColimitsOfSize_shrink.{0, w, 0, w} _
  have h₁ := isCoherent_tensor_free G hG P.relations.I
  have h₂ := isCoherent_tensor_free G hG P.generators.I
  have hcolim := CokernelCofork.mapIsColimit _ P.isColimit
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj G)
  have hck : IsCoherent (cokernel
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj G).map
        ((SheafOfModules.freeHomEquiv _).symm P.relations.s ≫ kernel.ι P.generators.π))) :=
    isCoherent_cokernel _
  exact isCoherent_of_iso' (M := cokernel
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj G).map
        ((SheafOfModules.freeHomEquiv _).symm P.relations.s ≫ kernel.ι P.generators.π)))
    (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel _) hcolim) hck

end Coherence

section Space

open Stacks.SheafOfModules

variable {X : Type u} [TopologicalSpace X]
  [(Opens.grothendieckTopology X).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [∀ U : Opens X, ((Opens.grothendieckTopology X).over U).HasSheafCompose
    (forget₂ CommRingCat.{u} RingCat.{u})]
  {O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

/-- **Stacks Project, Tag 01CE.** -/
@[stacks 01CE "tensor_finite_presentation_coherent, over a site, for sheafTensorRight"]
theorem isCoherent_tensorSheaf
    (F G : SheafOfModules.{u} (Stacks.commRingSheafToRingSheaf O))
    [F.IsFinitePresentation] (hG : IsCoherent G) :
    IsCoherent
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} O).flip.obj G).obj F) := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData F
  refine Site.isCoherent_opens_of_coversTop _ q.X q.coversTop fun i => ?_
  have hGi : Site.IsCoherent.{u, u, u} (G.over (q.X i)) :=
    Site.isCoherent_over_of_isCoherent_opens hG (q.X i)
  have key : Site.IsCoherent.{u, u, u}
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (O.over (q.X i))).flip.obj
        (G.over (q.X i))).obj (F.over (q.X i))) :=
    isCoherent_tensor_of_presentation (O := O.over (q.X i)) (G.over (q.X i))
      (F.over (q.X i)) hGi (q.presentation i) (hq.isFinite_presentation i)
  exact isCoherent_of_iso' (O := O.over (q.X i)) (tensorSheafOverIso F G (q.X i)) key

end Space

end Stacks.TensorCoherence

end
