module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.MonodromyEquivalence
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.DescentSheafExactness

/-!
# Descent along a Galois covering: exactness, and the sheaves it reaches

Let `G : A ⟶ X` be a Galois covering with group `H` (`AlgebraicGeometry.EtaleGaloisCovering`) and
`D(N)` the descent sheaf of a `Λ`-module `N` with an action `ρ` of `H`: its sections over an étale
`W ⟶ X` are the `H`-equivariant locally constant maps `W ×_X A → N`.

## Main definitions

* `AlgebraicGeometry.EtaleGaloisCovering.coverRep`: the action of `H` on the sections over the
  covering of a sheaf, through the restriction maps along the automorphisms of the covering.

## Main results

* `Stacks.Sheaf.exact_of_sections_exact`: a short complex of sheaves which is exact on the
  sections over every object is exact.
* `AlgebraicGeometry.EtaleGaloisCovering.shortExact_descentSheafMap`: `D` carries a short exact
  sequence of modules with `H`-action to a short exact sequence of sheaves.
* `AlgebraicGeometry.EtaleGaloisCovering.nonempty_iso_descentSheaf_coverRep`: a sheaf constant on
  a connected covering is the descent sheaf of its sections over the covering.
* `AlgebraicGeometry.EtaleGaloisCovering.nonempty_iso_constantSheaf_descentSheaf_one`: the descent
  sheaf of a module with trivial action is the constant sheaf.

## References

* [Stacks Project, Tag 0GJ0](https://stacks.math.columbia.edu/tag/0GJ0)
* [Stacks Project, Tag 0GIY](https://stacks.math.columbia.edu/tag/0GIY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u r w


namespace Stacks.Sheaf

/-- **A short complex of sheaves which is exact on the sections over every object is exact.** -/
theorem exact_of_sections_exact {C : Type*} [Category* C] (J : GrothendieckTopology C)
    {A : Type*} [Category* A] [Abelian A] [HasSheafify J A] (S : ShortComplex (Sheaf J A))
    (h : ∀ U : Cᵒᵖ, (S.map ((sheafSections J A).obj U)).Exact) : S.Exact := by
  refine S.exact_iff_epi_kernel_lift.mpr
    ⟨fun β γ hβγ ↦ Sheaf.hom_ext (NatTrans.ext (funext fun U ↦ ?_))⟩
  let E := (sheafSections J A).obj U
  have : PreservesFiniteLimits E :=
    comp_preservesFiniteLimits (sheafToPresheaf J A) ((evaluation _ _).obj U)
  have : Epi (kernel.lift (E.map S.g) (E.map S.f) (S.map E).zero) := (h U).epi_kernelLift
  have : Epi (E.map (kernel.lift S.g S.f S.zero)) := by
    rw [← epi_comp_iff_of_isIso _ (kernelComparison S.g E), map_lift_kernelComparison]
    infer_instance
  exact (cancel_epi (E.map (kernel.lift S.g S.f S.zero))).mp (congrArg (fun k ↦ k.hom.app U) hβγ)

end Stacks.Sheaf

namespace AlgebraicGeometry

namespace EtaleGaloisCovering

variable {X : Scheme.{u}} {H : Type w} [Group H] (G : EtaleGaloisCovering X H) {Λ : Type r}
  [Ring Λ]

/-! ### Functoriality in the module -/

section Map

variable {N N' : Type (max (u + 1) r)} [AddCommGroup N] [Module Λ N] [AddCommGroup N']
  [Module Λ N'] {ρ : H →* Module.End Λ N} {ρ' : H →* Module.End Λ N'}

/-- **Descent carries a short exact sequence of modules with `H`-action to a short exact sequence
of sheaves.** -/
theorem shortExact_descentSheafMap {N₁ N₂ N₃ : Type (max (u + 1) r)} [AddCommGroup N₁]
    [Module Λ N₁] [AddCommGroup N₂] [Module Λ N₂] [AddCommGroup N₃] [Module Λ N₃]
    {ρ₁ : H →* Module.End Λ N₁} {ρ₂ : H →* Module.End Λ N₂} {ρ₃ : H →* Module.End Λ N₃}
    (φ : N₁ →ₗ[Λ] N₂) (hφ : ∀ h x, φ (ρ₁ h x) = ρ₂ h (φ x))
    (ψ : N₂ →ₗ[Λ] N₃) (hψ : ∀ h x, ψ (ρ₂ h x) = ρ₃ h (ψ x))
    (hinj : Function.Injective φ) (hsurj : Function.Surjective ψ)
    (hex : LinearMap.range φ = LinearMap.ker ψ) :
    (ShortComplex.mk (G.descentSheafMap φ hφ) (G.descentSheafMap ψ hψ) (by
      rw [descentSheafMap_comp]
      ext W f
      refine Subtype.ext (LocallyConstant.ext fun z ↦ ?_)
      change ψ (φ (f.1 z)) = 0
      exact (LinearMap.mem_ker.1 (hex ▸ LinearMap.mem_range_self φ (f.1 z))))).ShortExact := by
  refine .mk' (Stacks.Sheaf.exact_of_sections_exact _ _ fun W ↦ ?_)
    (G.mono_descentSheafMap φ hφ hinj) (G.epi_descentSheafMap ψ hψ hsurj)
  refine (ShortComplex.moduleCat_exact_iff _).2 fun f hf ↦ ?_
  have hval : ∀ z, f.1 z ∈ LinearMap.range φ := fun z ↦ by
    rw [hex, LinearMap.mem_ker]
    exact congrArg (fun k : (G.descentPresheaf Λ N₃ ρ₃).obj W ↦ k.1 z) hf
  let e : N₂ → N₁ := Function.invFun φ
  have he : ∀ z, φ (e (f.1 z)) = f.1 z := fun z ↦ Function.invFun_eq (hval z)
  refine ⟨⟨f.1.map e, fun h z ↦ hinj ?_⟩, Subtype.ext (LocallyConstant.ext fun z ↦ he z)⟩
  show φ (e (f.1 _)) = φ (ρ₁ h (e (f.1 z)))
  rw [he, hφ, he]
  exact f.2 h z

end Map

/-! ### Sheaves constant on the covering -/

section Iso

/-- The automorphism of the covering given by `1 : H` is the identity. -/
theorem actHom_one : G.actHom 1 = 𝟙 G.cover :=
  MorphismProperty.Over.Hom.ext G.act_one

/-- The automorphism of the covering given by `a * b` is the composite of those given by `b`
and by `a`. -/
theorem actHom_mul (a b : H) : G.actHom (a * b) = G.actHom b ≫ G.actHom a :=
  MorphismProperty.Over.Hom.ext (G.act_mul a b)

variable {F F' : Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{max (u + 1) r} Λ)}
  {M M' : ModuleCat.{max (u + 1) r} Λ}

/-- **Two sheaves constant on the covering whose sections over the covering are equivariantly
isomorphic are isomorphic.** -/
theorem nonempty_iso_of_iso_app_cover
    (e : (constantSheaf ((Scheme.smallEtaleTopology X).over G.cover)
      (ModuleCat.{max (u + 1) r} Λ)).obj M ≅
        ((Scheme.smallEtaleTopology X).overPullback _ G.cover).obj F)
    (e' : (constantSheaf ((Scheme.smallEtaleTopology X).over G.cover)
      (ModuleCat.{max (u + 1) r} Λ)).obj M' ≅
        ((Scheme.smallEtaleTopology X).overPullback _ G.cover).obj F')
    (f : F.obj.obj (op G.cover) ≅ F'.obj.obj (op G.cover))
    (hf : ∀ h : H, F.obj.map (G.actHom h).op ≫ f.hom = f.hom ≫ F'.obj.map (G.actHom h).op) :
    Nonempty (F ≅ F') := by
  have hf' : ∀ h : H,
      F'.obj.map (G.actHom h).op ≫ f.inv = f.inv ≫ F.obj.map (G.actHom h).op := fun h ↦ by
    rw [Iso.comp_inv_eq, Category.assoc, hf h, Iso.inv_hom_id_assoc]
  obtain ⟨φ, hφ⟩ := G.exists_hom_app_cover_eq e f.hom hf
  obtain ⟨ψ, hψ⟩ := G.exists_hom_app_cover_eq e' f.inv hf'
  refine ⟨⟨φ, ψ, G.hom_ext e ?_, G.hom_ext e' ?_⟩⟩
  · show φ.hom.app _ ≫ ψ.hom.app _ = 𝟙 _
    rw [hφ, hψ, f.hom_inv_id]
  · show ψ.hom.app _ ≫ φ.hom.app _ = 𝟙 _
    rw [hφ, hψ, f.inv_hom_id]

/-- The action of `H` on the sections over the covering of a sheaf, through the restriction maps
along the automorphisms of the covering. -/
def coverRep (F : Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{max (u + 1) r} Λ)) :
    H →* Module.End Λ (F.obj.obj (op G.cover)) where
  toFun h := (F.obj.map (G.actHom h⁻¹).op).hom
  map_one' := by
    rw [inv_one, G.actHom_one, op_id, F.obj.map_id]
    rfl
  map_mul' a b := by
    rw [mul_inv_rev, G.actHom_mul, op_comp, F.obj.map_comp]
    rfl

/-- `h : H` acts on the sections over the covering by restriction along the automorphism given by
`h⁻¹`. -/
theorem coverRep_apply (h : H) (x : F.obj.obj (op G.cover)) :
    G.coverRep F h x = (F.obj.map (G.actHom h⁻¹).op).hom x :=
  rfl

/-- **A sheaf constant on a connected covering is the descent sheaf of its sections over the
covering**, with `H` acting through the restriction maps along the automorphisms of the
covering. -/
theorem nonempty_iso_descentSheaf_coverRep [ConnectedSpace G.cover.left]
    (e : (constantSheaf ((Scheme.smallEtaleTopology X).over G.cover)
      (ModuleCat.{max (u + 1) r} Λ)).obj M ≅
        ((Scheme.smallEtaleTopology X).overPullback _ G.cover).obj F) :
    Nonempty (F ≅ G.descentSheaf Λ (F.obj.obj (op G.cover)) (G.coverRep F)) := by
  let N := F.obj.obj (op G.cover)
  let ε := G.descentSectionsEquiv (Λ := Λ) N (G.coverRep F)
  refine G.nonempty_iso_of_iso_app_cover e (G.trivialization Λ N (G.coverRep F)) ε.symm.toModuleIso
    fun h ↦ ?_
  ext n
  apply ε.injective
  show ε (ε.symm ((F.obj.map (G.actHom h).op).hom n)) =
    ε (((G.descentPresheaf Λ N (G.coverRep F)).map (G.actHom h).op).hom (ε.symm n))
  rw [G.descentSectionsEquiv_map_actHom, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply, coverRep_apply, inv_inv]

/-- **The descent sheaf of a module with trivial action on a connected covering is the constant
sheaf.** -/
theorem nonempty_iso_constantSheaf_descentSheaf_one [ConnectedSpace G.cover.left]
    (N : Type (max (u + 1) r)) [AddCommGroup N] [Module Λ N] :
    Nonempty (G.descentSheaf Λ N 1 ≅ (constantSheaf (Scheme.smallEtaleTopology X)
      (ModuleCat.{max (u + 1) r} Λ)).obj (ModuleCat.of Λ N)) := by
  let J := Scheme.smallEtaleTopology X
  let ε := G.descentSectionsEquiv (Λ := Λ) N 1
  let t := (toSheafify J ((Functor.const (X.Etale)ᵒᵖ).obj (ModuleCat.of Λ N))).app (op G.cover)
  have ht : Function.Bijective t.hom :=
    Scheme.bijective_toSheafify_const_app_of_irreducibleSpace Λ (ModuleCat.of Λ N) G.cover
  let τ : N ≃ₗ[Λ] ((constantSheaf J (ModuleCat.{max (u + 1) r} Λ)).obj
      (ModuleCat.of Λ N)).obj.obj (op G.cover) := LinearEquiv.ofBijective t.hom ht
  have hnat : ∀ (h : H) (n : N), (((constantSheaf J (ModuleCat.{max (u + 1) r} Λ)).obj
      (ModuleCat.of Λ N)).obj.map (G.actHom h).op).hom (τ n) = τ n := fun h n ↦
    (ConcreteCategory.congr_hom ((toSheafify J ((Functor.const (X.Etale)ᵒᵖ).obj
      (ModuleCat.of Λ N))).naturality (G.actHom h).op) n).symm
  refine G.nonempty_iso_of_iso_app_cover (G.trivialization Λ N 1)
    ((Stacks.ConstantSheaf.overPullbackConstantSheafIso J (ModuleCat.{max (u + 1) r} Λ)
      G.cover).app (ModuleCat.of Λ N)) (ε.trans τ).toModuleIso fun h ↦ ?_
  ext d
  show τ (ε (((G.descentPresheaf Λ N 1).map (G.actHom h).op).hom d)) =
    (((constantSheaf J (ModuleCat.{max (u + 1) r} Λ)).obj (ModuleCat.of Λ N)).obj.map
      (G.actHom h).op).hom (τ (ε d))
  rw [hnat, G.descentSectionsEquiv_map_actHom]
  rfl

end Iso

end EtaleGaloisCovering

end AlgebraicGeometry

end
