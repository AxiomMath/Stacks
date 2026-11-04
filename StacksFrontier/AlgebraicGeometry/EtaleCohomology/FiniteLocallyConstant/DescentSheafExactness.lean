module
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantModuleSheafIrreducibleSectionsRing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantModuleSheafSliceSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.GaloisCoverDescent
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategories.FiberFunctor
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.RingTheory.Etale.Basic
public import StacksFrontier.RingTheory.FinitePresentation.ModuleDescent

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.MonodromyEquivalence

/-!
# Exactness of descent along a Galois covering

Let `A ⟶ X` be a Galois covering with group `H` (`AlgebraicGeometry.EtaleGaloisCovering`), with
`A` connected. For a `Λ`-module `N` with an action of `H`, the descent sheaf `D(N)` is the sheaf
of `H`-equivariant locally constant maps `W ×_X A → N`. This file shows that `N ↦ D(N)` is an
exact functor, that it carries a module with trivial action to the constant sheaf, and that every
sheaf constant on `A` is the descent sheaf of its sections over `A`.

## Main definitions

* `AlgebraicGeometry.EtaleGaloisCovering.sectionsRepresentation` — the action of `H` on the
  sections over the covering of a sheaf.
* `AlgebraicGeometry.EtaleGaloisCovering.descentSheafMap` — the morphism `D(N₁) ⟶ D(N₂)`
  induced by an equivariant linear map.

## Main results

* `AlgebraicGeometry.EtaleGaloisCovering.nonempty_iso_of_cover` — two sheaves constant on the
  covering whose sections over the covering are equivariantly isomorphic are isomorphic.
* `AlgebraicGeometry.EtaleGaloisCovering.nonempty_iso_descentSheaf` — a sheaf constant on the
  covering is the descent sheaf of its sections over the covering.
* `AlgebraicGeometry.EtaleGaloisCovering.mono_descentSheafMap`,
  `AlgebraicGeometry.EtaleGaloisCovering.epi_descentSheafMap` and
  `AlgebraicGeometry.EtaleGaloisCovering.cokernelDescentSheafMapIso` — exactness of `D`.
* `AlgebraicGeometry.EtaleGaloisCovering.nonempty_descentSheaf_iso_constantSheaf` — `D(W)` is the
  constant sheaf `W̲` when `H` acts trivially on `W`.

## References

* [Stacks Project, Tag 0GIY](https://stacks.math.columbia.edu/tag/0GIY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u r w

namespace AlgebraicGeometry.EtaleGaloisCovering

variable {X : Scheme.{u}} {H : Type w} [Group H] (G : EtaleGaloisCovering X H) {Λ : Type r}
  [Ring Λ]

/-! ### The action on the sections over the covering -/

section Representation

variable (P : Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ))

/-- **The action of `H` on the sections over the covering of a sheaf**: `h` acts by restriction
along the automorphism `h⁻¹` of the covering, which makes it a left action. -/
def sectionsRepresentation : H →* Module.End Λ (P.obj.obj (op G.cover)) where
  toFun h := (P.obj.map (G.actHom h⁻¹).op).hom
  map_one' := by
    have h1 : G.actHom 1⁻¹ = 𝟙 G.cover := by
      apply MorphismProperty.Over.Hom.ext
      change G.act 1⁻¹ = 𝟙 _
      rw [inv_one, G.act_one]
    rw [h1, op_id, P.obj.map_id]
    rfl
  map_mul' h h' := by
    have h1 : G.actHom (h * h')⁻¹ = G.actHom h⁻¹ ≫ G.actHom h'⁻¹ := by
      apply MorphismProperty.Over.Hom.ext
      change G.act (h * h')⁻¹ = G.act h⁻¹ ≫ G.act h'⁻¹
      rw [mul_inv_rev, G.act_mul]
    rw [h1, op_comp, P.obj.map_comp]
    rfl

/-- `h` acts on the sections over the covering by restriction along `h⁻¹`. -/
theorem sectionsRepresentation_apply (h : H) (x : P.obj.obj (op G.cover)) :
    G.sectionsRepresentation P h x = P.obj.map (G.actHom h⁻¹).op x :=
  rfl

end Representation

/-! ### Sheaves constant on the covering -/

section Comparison

variable [ConnectedSpace G.cover.left]
  {P Q : Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)}
  {M M' : ModuleCat.{max (u + 1) r} Λ}

omit [ConnectedSpace G.cover.left] in
/-- **Two sheaves constant on the covering whose sections over the covering are equivariantly
isomorphic are isomorphic.** Both the isomorphism and its inverse extend to morphisms of sheaves,
and the composites are the identity because they are so over the covering. -/
theorem nonempty_iso_of_cover
    (eP : (constantSheaf (X.smallEtaleTopology.over G.cover)
      (ModuleCat.{max (u + 1) r} Λ)).obj M ≅ (X.smallEtaleTopology.overPullback _ G.cover).obj P)
    (eQ : (constantSheaf (X.smallEtaleTopology.over G.cover)
      (ModuleCat.{max (u + 1) r} Λ)).obj M' ≅ (X.smallEtaleTopology.overPullback _ G.cover).obj Q)
    (E : P.obj.obj (op G.cover) ≃ₗ[Λ] Q.obj.obj (op G.cover))
    (hE : ∀ (h : H) (x : P.obj.obj (op G.cover)),
      E (P.obj.map (G.actHom h).op x) = Q.obj.map (G.actHom h).op (E x)) :
    Nonempty (P ≅ Q) := by
  obtain ⟨α, hα⟩ := G.exists_hom_app_cover_eq eP (ModuleCat.ofHom E.toLinearMap) (fun h ↦ by
    ext x
    exact hE h x)
  obtain ⟨β, hβ⟩ := G.exists_hom_app_cover_eq eQ (ModuleCat.ofHom E.symm.toLinearMap)
    (fun h ↦ by
      ext y
      apply E.injective
      change E (E.symm (Q.obj.map (G.actHom h).op y)) =
        E (P.obj.map (G.actHom h).op (E.symm y))
      rw [hE, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply])
  refine ⟨⟨α, β, G.hom_ext eP ?_, G.hom_ext eQ ?_⟩⟩
  all_goals
    change _ ≫ _ = 𝟙 _
    rw [hα, hβ]
    ext x
    simp

/-- **A sheaf constant on the covering is the descent sheaf of its sections over the covering**,
with the action `sectionsRepresentation`. -/
theorem nonempty_iso_descentSheaf
    (eP : (constantSheaf (X.smallEtaleTopology.over G.cover)
      (ModuleCat.{max (u + 1) r} Λ)).obj M ≅ (X.smallEtaleTopology.overPullback _ G.cover).obj P) :
    Nonempty (P ≅ G.descentSheaf Λ (P.obj.obj (op G.cover)) (G.sectionsRepresentation P)) := by
  let ρ := G.sectionsRepresentation P
  let E := G.descentSectionsEquiv (P.obj.obj (op G.cover)) ρ
  refine G.nonempty_iso_of_cover eP (G.trivialization Λ _ ρ) E.symm fun h x ↦ ?_
  apply E.injective
  change E (E.symm (P.obj.map (G.actHom h).op x)) =
    E (((G.descentPresheaf Λ _ ρ).map (G.actHom h).op).hom (E.symm x))
  rw [descentSectionsEquiv_map_actHom, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply, sectionsRepresentation_apply, inv_inv]

end Comparison

/-! ### Functoriality of the descent sheaf -/

section Functoriality

variable {N₁ N₂ N₃ : Type (max (u + 1) r)} [AddCommGroup N₁] [Module Λ N₁] [AddCommGroup N₂]
  [Module Λ N₂] [AddCommGroup N₃] [Module Λ N₃] {ρ₁ : H →* Module.End Λ N₁}
  {ρ₂ : H →* Module.End Λ N₂} {ρ₃ : H →* Module.End Λ N₃}

/-- Post-composition with an equivariant linear map, on equivariant locally constant maps. -/
def equivariantMapsMap (φ : N₁ →ₗ[Λ] N₂) (hφ : ∀ (h : H) (x : N₁), φ (ρ₁ h x) = ρ₂ h (φ x))
    (W : X.Etale) : G.equivariantMaps Λ N₁ ρ₁ W →ₗ[Λ] G.equivariantMaps Λ N₂ ρ₂ W where
  toFun f := ⟨f.1.map φ, fun h z ↦ by
    change φ (f.1 ((G.pullbackAct W h).base z)) = ρ₂ h (φ (f.1 z))
    rw [f.2 h z, hφ]⟩
  map_add' f g := Subtype.ext (LocallyConstant.ext fun z ↦ map_add φ (f.1 z) (g.1 z))
  map_smul' c f := Subtype.ext (LocallyConstant.ext fun z ↦ map_smul φ c (f.1 z))

/-- **The morphism of descent sheaves `D(N₁) ⟶ D(N₂)` induced by an equivariant linear map.** -/
def descentSheafMap (φ : N₁ →ₗ[Λ] N₂) (hφ : ∀ (h : H) (x : N₁), φ (ρ₁ h x) = ρ₂ h (φ x)) :
    G.descentSheaf Λ N₁ ρ₁ ⟶ G.descentSheaf Λ N₂ ρ₂ :=
  ObjectProperty.homMk
    { app W := ModuleCat.ofHom (G.equivariantMapsMap φ hφ W.unop)
      naturality _ _ _ := rfl }

/-- On sections, `D(φ)` is post-composition with `φ`. -/
theorem descentSheafMap_app_apply (φ : N₁ →ₗ[Λ] N₂)
    (hφ : ∀ (h : H) (x : N₁), φ (ρ₁ h x) = ρ₂ h (φ x)) (W : (X.Etale)ᵒᵖ)
    (f : (G.descentSheaf Λ N₁ ρ₁).obj.obj W) (z : G.fiberProd W.unop) :
    (((G.descentSheafMap φ hφ).hom.app W) f).1 z = φ (f.1 z) :=
  rfl

/-- `D` preserves composition: `D(φ) ≫ D(ψ) = D(ψ ∘ φ)`. -/
theorem descentSheafMap_comp (φ : N₁ →ₗ[Λ] N₂)
    (hφ : ∀ (h : H) (x : N₁), φ (ρ₁ h x) = ρ₂ h (φ x)) (ψ : N₂ →ₗ[Λ] N₃)
    (hψ : ∀ (h : H) (x : N₂), ψ (ρ₂ h x) = ρ₃ h (ψ x)) :
    G.descentSheafMap φ hφ ≫ G.descentSheafMap ψ hψ =
      G.descentSheafMap (ψ ∘ₗ φ) (fun h x ↦ by
        rw [LinearMap.comp_apply, LinearMap.comp_apply, hφ, hψ]) :=
  rfl

/-- **An injective equivariant map induces a monomorphism of descent sheaves**: it is injective on
sections. -/
theorem mono_descentSheafMap (φ : N₁ →ₗ[Λ] N₂)
    (hφ : ∀ (h : H) (x : N₁), φ (ρ₁ h x) = ρ₂ h (φ x)) (hinj : Function.Injective φ) :
    Mono (G.descentSheafMap φ hφ) := by
  have h : ∀ W, Mono ((G.descentSheafMap φ hφ).hom.app W) := fun W ↦
    (ModuleCat.mono_iff_injective _).2 fun f g hfg ↦ Subtype.ext (LocallyConstant.ext fun z ↦
      hinj (congrArg (fun k : (G.descentSheaf Λ N₂ ρ₂).obj.obj W ↦ k.1 z) hfg))
  have : Mono (G.descentSheafMap φ hφ).hom := NatTrans.mono_of_mono_app _
  exact Sheaf.Hom.mono_of_presheaf_mono _ _ _

/-- Over an object over the covering, a surjective equivariant map induces a surjection on
sections of descent sheaves: there the sections are all locally constant maps. -/
theorem surjective_descentSheafMap_app (ψ : N₂ →ₗ[Λ] N₃)
    (hψ : ∀ (h : H) (x : N₂), ψ (ρ₂ h x) = ρ₃ h (ψ x)) (hsurj : Function.Surjective ψ)
    (T : Over G.cover) :
    Function.Surjective ((G.descentSheafMap ψ hψ).hom.app (op T.left)) := by
  intro s
  obtain ⟨t, ht⟩ := (G.bijective_restrictGraph Λ N₂ ρ₂ T).2
    ((G.restrictGraph Λ N₃ ρ₃ T s).map (Function.surjInv hsurj))
  refine ⟨t, (G.bijective_restrictGraph Λ N₃ ρ₃ T).1 (LocallyConstant.ext fun y ↦ ?_)⟩
  change ψ (G.restrictGraph Λ N₂ ρ₂ T t y) = G.restrictGraph Λ N₃ ρ₃ T s y
  rw [ht]
  exact Function.surjInv_eq hsurj _

/-- **A surjective equivariant map induces an epimorphism of descent sheaves**: it is surjective
on sections over the objects over the covering, which cover every object. -/
theorem epi_descentSheafMap (ψ : N₂ →ₗ[Λ] N₃)
    (hψ : ∀ (h : H) (x : N₂), ψ (ρ₂ h x) = ρ₃ h (ψ x)) (hsurj : Function.Surjective ψ) :
    Epi (G.descentSheafMap ψ hψ) := by
  have : Sheaf.IsLocallySurjective (G.descentSheafMap ψ hψ) := ⟨fun {W} s ↦ by
    refine X.smallEtaleTopology.superset_covering ?_ (G.ofArrows_fiberObjFst_mem W)
    rintro V _ ⟨Z, k, _, ⟨⟩, rfl⟩
    refine Sieve.downward_closed _ ?_ k
    obtain ⟨t, ht⟩ := G.surjective_descentSheafMap_app ψ hψ hsurj (Over.mk (G.fiberObjSnd W))
      ((G.descentSheaf Λ N₃ ρ₃).obj.map (G.fiberObjFst W).op s)
    exact ⟨t, ht⟩⟩
  infer_instance

/-- **The kernel of `D(ψ)` is `D(φ)`** for an exact sequence `N₁ → N₂ → N₃` with `φ`
injective: a section of `D(N₂)` killed by `ψ` takes values in the image of `φ`. -/
def isLimitDescentSheafMap (φ : N₁ →ₗ[Λ] N₂)
    (hφ : ∀ (h : H) (x : N₁), φ (ρ₁ h x) = ρ₂ h (φ x)) (ψ : N₂ →ₗ[Λ] N₃)
    (hψ : ∀ (h : H) (x : N₂), ψ (ρ₂ h x) = ρ₃ h (ψ x)) (hinj : Function.Injective φ)
    (hexact : ∀ y, ψ y = 0 → ∃ x, φ x = y) (hzero : ∀ x, ψ (φ x) = 0) :
    IsLimit (KernelFork.ofι (G.descentSheafMap φ hφ) (f := G.descentSheafMap ψ hψ) (by
      rw [descentSheafMap_comp]
      apply (sheafToPresheaf _ _).map_injective
      rw [Functor.map_zero]
      ext W f
      exact Subtype.ext (LocallyConstant.ext fun z ↦ hzero (f.1 z)))) := by
  have := G.mono_descentSheafMap φ hφ hinj
  refine KernelFork.IsLimit.ofι' _ _ fun {Z} k hk ↦ ?_
  let g : N₂ → N₁ := Function.invFun φ
  have hg : ∀ y, ψ y = 0 → φ (g y) = y := fun y hy ↦ Function.invFun_eq (hexact y hy)
  have hk' : ∀ (W : (X.Etale)ᵒᵖ) (z : Z.obj.obj W) (p : G.fiberProd W.unop),
      ψ ((k.hom.app W z).1 p) = 0 := fun W z p ↦
    congrArg (fun m : Z ⟶ G.descentSheaf Λ N₃ ρ₃ ↦ (m.hom.app W z).1 p) hk
  have hval : ∀ (W : (X.Etale)ᵒᵖ) (z : Z.obj.obj W) (p : G.fiberProd W.unop),
      φ (g ((k.hom.app W z).1 p)) = (k.hom.app W z).1 p := fun W z p ↦ hg _ (hk' W z p)
  let lapp : ∀ W : (X.Etale)ᵒᵖ, Z.obj.obj W →ₗ[Λ] G.equivariantMaps Λ N₁ ρ₁ W.unop := fun W ↦
    { toFun z := ⟨(k.hom.app W z).1.map g, fun h p ↦ hinj (by
        change φ (g ((k.hom.app W z).1 ((G.pullbackAct W.unop h).base p))) =
          φ (ρ₁ h (g ((k.hom.app W z).1 p)))
        rw [hval, hφ, hval]
        exact (k.hom.app W z).2 h p)⟩
      map_add' z z' := Subtype.ext (LocallyConstant.ext fun p ↦ hinj (by
        change φ (g ((k.hom.app W (z + z')).1 p)) =
          φ (g ((k.hom.app W z).1 p) + g ((k.hom.app W z').1 p))
        rw [hval, map_add φ, hval, hval]
        exact congrArg (fun f : (G.descentSheaf Λ N₂ ρ₂).obj.obj W ↦ f.1 p)
          (map_add (k.hom.app W).hom z z')))
      map_smul' c z := Subtype.ext (LocallyConstant.ext fun p ↦ hinj (by
        change φ (g ((k.hom.app W (c • z)).1 p)) = φ (c • g ((k.hom.app W z).1 p))
        rw [hval, map_smul φ, hval]
        exact congrArg (fun f : (G.descentSheaf Λ N₂ ρ₂).obj.obj W ↦ f.1 p)
          (map_smul (k.hom.app W).hom c z))) }
  refine ⟨ObjectProperty.homMk
    { app W := ModuleCat.ofHom (lapp W)
      naturality W W' m := by
        ext z
        refine Subtype.ext (LocallyConstant.ext fun p ↦ hinj ?_)
        change φ (g ((k.hom.app W' (Z.obj.map m z)).1 p)) =
          φ (g ((k.hom.app W z).1 ((G.pullbackMap m.unop).base p)))
        rw [hval, hval]
        exact congrArg (fun f : (G.descentSheaf Λ N₂ ρ₂).obj.obj W' ↦ f.1 p)
          (ConcreteCategory.congr_hom (k.hom.naturality m) z) }, ?_⟩
  ext W z
  exact Subtype.ext (LocallyConstant.ext fun p ↦ hval W z p)

/-- **`D` carries a short exact sequence to a cokernel**: for an exact sequence
`0 → N₁ → N₂ → N₃ → 0` of modules with an action of `H`, the cokernel of `D(N₁) ⟶ D(N₂)` is
`D(N₃)`. -/
def cokernelDescentSheafMapIso (φ : N₁ →ₗ[Λ] N₂)
    (hφ : ∀ (h : H) (x : N₁), φ (ρ₁ h x) = ρ₂ h (φ x)) (ψ : N₂ →ₗ[Λ] N₃)
    (hψ : ∀ (h : H) (x : N₂), ψ (ρ₂ h x) = ρ₃ h (ψ x)) (hinj : Function.Injective φ)
    (hsurj : Function.Surjective ψ) (hexact : ∀ y, ψ y = 0 → ∃ x, φ x = y)
    (hzero : ∀ x, ψ (φ x) = 0) :
    cokernel (G.descentSheafMap φ hφ) ≅ G.descentSheaf Λ N₃ ρ₃ :=
  haveI := G.epi_descentSheafMap ψ hψ hsurj
  (colimit.isColimit _).coconePointUniqueUpToIso
    (Abelian.epiIsCokernelOfKernel _
      (G.isLimitDescentSheafMap φ hφ ψ hψ hinj hexact hzero))

/-- **The descent sheaf of a module with no elements but zero is zero.** -/
theorem isZero_descentSheaf [Subsingleton N₁] : IsZero (G.descentSheaf Λ N₁ ρ₁) := by
  have h : ∀ W, Subsingleton ((G.descentSheaf Λ N₁ ρ₁).obj.obj W) := fun W ↦
    ⟨fun f g ↦ Subtype.ext (LocallyConstant.ext fun z ↦ Subsingleton.elim _ _)⟩
  exact IsZero.of_full_of_faithful_of_isZero (sheafToPresheaf _ _) _
    ((Functor.isZero_iff _).2 fun W ↦ @ModuleCat.isZero_of_subsingleton _ _ _ (h W))

/-- **An equivariant isomorphism induces an isomorphism of descent sheaves.** -/
theorem isIso_descentSheafMap (φ : N₁ →ₗ[Λ] N₂)
    (hφ : ∀ (h : H) (x : N₁), φ (ρ₁ h x) = ρ₂ h (φ x)) (hbij : Function.Bijective φ) :
    IsIso (G.descentSheafMap φ hφ) :=
  have := G.mono_descentSheafMap φ hφ hbij.1
  have := G.epi_descentSheafMap φ hφ hbij.2
  isIso_of_mono_of_epi _

end Functoriality

/-! ### Trivial actions -/

section Trivial

variable [ConnectedSpace G.cover.left] (W : Type (max (u + 1) r)) [AddCommGroup W]
  [Module Λ W]

/-- **The descent sheaf of a module on which `H` acts trivially is the constant sheaf.** Both are
constant on the covering, with sections `W` over it, on which `H` acts trivially. -/
theorem nonempty_descentSheaf_iso_constantSheaf (ρ : H →* Module.End Λ W)
    (hρ : ∀ h : H, ρ h = 1) :
    Nonempty (G.descentSheaf Λ W ρ ≅
      (constantSheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).obj
        (ModuleCat.of Λ W)) := by
  let K := (constantSheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).obj
    (ModuleCat.of Λ W)
  let c := (toSheafify X.smallEtaleTopology
    ((Functor.const (X.Etale)ᵒᵖ).obj (ModuleCat.of Λ W))).app (op G.cover)
  have hc : Function.Bijective c :=
    Scheme.bijective_toSheafify_const_app_of_irreducibleSpace Λ (ModuleCat.of Λ W) G.cover
  let cE : W ≃ₗ[Λ] K.obj.obj (op G.cover) := LinearEquiv.ofBijective c.hom hc
  let E := G.descentSectionsEquiv W ρ
  have hK : ∀ (h : H) (y : K.obj.obj (op G.cover)), K.obj.map (G.actHom h).op y = y := by
    intro h y
    obtain ⟨m, rfl⟩ := hc.2 y
    exact (ConcreteCategory.congr_hom
      ((toSheafify X.smallEtaleTopology
        ((Functor.const (X.Etale)ᵒᵖ).obj (ModuleCat.of Λ W))).naturality (G.actHom h).op) m).symm
  refine G.nonempty_iso_of_cover (G.trivialization Λ W ρ)
    ((Stacks.ConstantSheaf.overPullbackConstantSheafIso X.smallEtaleTopology
      (ModuleCat.{max (u + 1) r} Λ) G.cover).app (ModuleCat.of Λ W)) (E.trans cE)
    fun h d ↦ ?_
  rw [hK]
  change cE (E (((G.descentPresheaf Λ W ρ).map (G.actHom h).op).hom d)) = cE (E d)
  rw [descentSectionsEquiv_map_actHom, hρ]
  rfl

end Trivial

end AlgebraicGeometry.EtaleGaloisCovering

end
