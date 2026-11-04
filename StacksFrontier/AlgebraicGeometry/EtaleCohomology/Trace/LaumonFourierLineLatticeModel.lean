module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFamilyFibreCharacter
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFourierLineFamily
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.SectionNormalRange

/-!
# The model of Laumon's Fourier family over `k` and its fundamental groups

The Fourier family of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH) at `(k', a₀)` lives on
`Spec k'[x][t]`, with kernel `a₀ xⁿ + x t`. Its model over `k` lives on `Spec k[a][x][t]`, with
kernel `a xⁿ + x t` (`Stacks.EtaleCohomology.laumonModelKernel`); the plane `a = a₀` over `k'` maps
to the model by `a ↦ a₀` (`Stacks.EtaleCohomology.laumonParamPlaneAlgHom`), carrying the kernel of
the model to the kernel of the family and commuting with the first projections
(`Stacks.EtaleCohomology.laumonParamPlane_comp_laumonModelPr₁`). On fundamental groups:

* `pr₁_* : π₁(𝔸²_{k'}) → π₁(𝔸¹_{k'})` is surjective (the section `t = 0`);
* the image of `π₁(𝔸¹_{k'}) → π₁(U)`, `U ≅ 𝔸¹_k`, is normal (`𝔸¹_{k'} = 𝔸¹_k ×_k k'`);
* the two routes `π₁(𝔸²_{k'}) → π₁(U)`, through the model and through `𝔸¹_{k'}`, are inner
  conjugate (`Stacks.EtaleCohomology.exists_conj_laumonModelPr₁`);
* the Artin–Schreier character of the family, for `ψ' = ψ ∘ Tr_{k'/k}`, is the character of the
  model read along `π₁(𝔸²_{k'}) → π₁(model)`
  (`Stacks.EtaleCohomology.artinSchreierCharacter_laumonModel`).

## Main definitions

* `Stacks.EtaleCohomology.laumonModelKernel`, `Stacks.EtaleCohomology.laumonModelPr₁`,
  `Stacks.EtaleCohomology.laumonParamPlaneAlgHom`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

section Ring

variable (k : Type u) [Field k]

/-- **The kernel `a xⁿ + x t` of the model**, in `k[a][x][t]` (`a` innermost, `t` outermost). -/
def laumonModelKernel (n : ℕ) : Polynomial (Polynomial (Polynomial k)) :=
  C (C Polynomial.X * Polynomial.X ^ n) + C Polynomial.X * Polynomial.X

/-- **The first projection `Spec k[a][x][t] → Spec k[x]` of the model.** -/
abbrev laumonModelPr₁ :
    Spec (.of (Polynomial (Polynomial (Polynomial k)))) ⟶ Spec (.of (Polynomial k)) :=
  Spec.map (CommRingCat.ofHom ((C : Polynomial (Polynomial k) →+* _).comp
    (mapRingHom (C : k →+* Polynomial k))))

variable (k' : Type u) [Field k'] [Algebra k k'] (a : k')

/-- **`a ↦ a₀`, `k[a][x][t] → k'[x][t]`**, as a homomorphism of `k`-algebras. -/
def laumonParamPlaneAlgHom :
    Polynomial (Polynomial (Polynomial k)) →ₐ[k] Polynomial (Polynomial k') :=
  { mapRingHom (mapRingHom (eval₂RingHom (algebraMap k k') a)) with
    commutes' := fun c => by
      change mapRingHom (mapRingHom (eval₂RingHom (algebraMap k k') a)) (C (C (C c))) =
        C (C (algebraMap k k' c))
      simp }

/-- The ring homomorphism underlying `laumonParamPlaneAlgHom` is the coefficientwise map
`mapRingHom (mapRingHom (eval₂RingHom (algebraMap k k') a))`. -/
theorem laumonParamPlaneAlgHom_toRingHom :
    (laumonParamPlaneAlgHom k k' a).toRingHom =
      mapRingHom (mapRingHom (eval₂RingHom (algebraMap k k') a)) :=
  rfl

/-- **`a ↦ a₀` carries the kernel of the model to the kernel of the family.** -/
theorem laumonParamPlaneAlgHom_laumonModelKernel (n : ℕ) :
    laumonParamPlaneAlgHom k k' a (laumonModelKernel k n) = laumonFourierKernel k' n a := by
  change mapRingHom (mapRingHom (eval₂RingHom (algebraMap k k') a)) (laumonModelKernel k n) = _
  simp [laumonModelKernel, laumonFourierKernel]

/-- **The plane `a = a₀` and the model have compatible first projections.** -/
theorem laumonParamPlane_comp_laumonModelPr₁ :
    Spec.map (CommRingCat.ofHom (mapRingHom (mapRingHom (eval₂RingHom (algebraMap k k') a)))) ≫
        laumonModelPr₁ k =
      laumonFamilyPr₁ k' ≫ Spec.map (CommRingCat.ofHom (mapRingHom (algebraMap k k'))) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  refine Polynomial.ringHom_ext (fun c => ?_) ?_ <;> simp

/-- The section `t = 0` of `pr₁ : Spec k'[x][t] → Spec k'[x]`. -/
theorem laumonFamilyPr₁_section :
    Spec.map (CommRingCat.ofHom (evalRingHom (0 : Polynomial k'))) ≫ laumonFamilyPr₁ k' = 𝟙 _ := by
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1
  apply CommRingCat.hom_ext
  refine Polynomial.ringHom_ext (fun c => ?_) ?_ <;> simp

end Ring

section FundamentalGroup

variable (k : Type u) [Field k] (k' : Type u) [Field k'] [Algebra k k'] (a : k')

/-- **`pr₁_*` is surjective** on the fundamental group of the plane over `k'`. -/
theorem surjective_etaleFundamentalGroupMap_laumonFamilyPr₁
    (z : GeometricPoint (Spec (.of (Polynomial (Polynomial k'))))) :
    Function.Surjective (etaleFundamentalGroupMap (laumonFamilyPr₁ k') z) :=
  surjective_etaleFundamentalGroupMap_of_section _ _ (laumonFamilyPr₁_section k') z

/-- **The image of `π₁(𝔸¹_{k'}) → π₁(U)` is normal**, for `U ≅ 𝔸¹_k` over a finite field `k` and a
finite extension `k'`. -/
theorem normal_range_laumonLineFieldExtension [Finite k] [Module.Finite k k'] {U : Scheme.{u}}
    [ConnectedSpace U] (f : U ⟶ Spec (.of k)) (e : U ⟶ Spec (.of (Polynomial k))) [IsIso e]
    (hef : e ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) = f)
    (y : GeometricPoint (Spec (.of (Polynomial k')))) {x : GeometricPoint U}
    (hz : y.map (Spec.map (CommRingCat.ofHom (mapRingHom (algebraMap k k'))) ≫ inv e) = x) :
    (hz ▸ (etaleFundamentalGroupMap (Spec.map (CommRingCat.ofHom (mapRingHom (algebraMap k k'))) ≫
      inv e) y).toMonoidHom).range.Normal := by
  subst hz
  have hpb : IsPullback (Spec.map (CommRingCat.ofHom (mapRingHom (algebraMap k k'))) ≫ inv e)
      (Spec.map (CommRingCat.ofHom (algebraMap k' (Polynomial k')))) f (specAlgebraMap k k') :=
    (isPullback_specMap_polynomial_mapRingHom k k').of_iso (Iso.refl _)
      (asIso e).symm (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp [← hef]) (by simp)
  exact normal_range_etaleFundamentalGroupMap_of_isPullback f _ _ hpb y

/-- **The two routes from the plane over `k'` to `U` are inner conjugate**: through the model
`Spec k[a][x][t]` and its first projection, and through the first projection to `𝔸¹_{k'}` and
`𝔸¹_{k'} → 𝔸¹_k ≅ U`, for any changes of base point. -/
theorem exists_conj_laumonModelPr₁ {U : Scheme.{u}} [ConnectedSpace U]
    (e : U ⟶ Spec (.of (Polynomial k))) [IsIso e] {x : GeometricPoint U}
    (z : GeometricPoint (Spec (.of (Polynomial (Polynomial k')))))
    (hz : (z.map (laumonFamilyPr₁ k')).map
      (Spec.map (CommRingCat.ofHom (mapRingHom (algebraMap k k'))) ≫ inv e) = x)
    (wm : GeometricPoint (Spec (.of (Polynomial (Polynomial (Polynomial k))))))
    (t₀ : finiteEtaleFiberFunctor x ≅ finiteEtaleFiberFunctor (wm.map (laumonModelPr₁ k ≫ inv e)))
    (t : finiteEtaleFiberFunctor wm ≅ finiteEtaleFiberFunctor (z.map (Spec.map (CommRingCat.ofHom
      (mapRingHom (mapRingHom (eval₂RingHom (algebraMap k k') a))))))) :
    ∃ γ : EtaleFundamentalGroup U x, ∀ g,
      (etaleFundamentalGroupBasePointHom t₀) (etaleFundamentalGroupMap (laumonModelPr₁ k ≫ inv e) wm
        ((etaleFundamentalGroupBasePointHom t) (etaleFundamentalGroupMap (Spec.map
          (CommRingCat.ofHom (mapRingHom (mapRingHom (eval₂RingHom (algebraMap k k') a))))) z g))) =
      γ * (hz ▸ (etaleFundamentalGroupMap
        (Spec.map (CommRingCat.ofHom (mapRingHom (algebraMap k k'))) ≫ inv e)
          (z.map (laumonFamilyPr₁ k'))).toMonoidHom)
        (etaleFundamentalGroupMap (laumonFamilyPr₁ k') z g) *
        γ⁻¹ := by
  have h₁ := (((isEtaleFundamentalGroupHomInducedBy_map _ z).comp_baseChange
    (isEtaleFundamentalGroupHomInducedBy_basePointHom_id t)).comp_baseChange
      (isEtaleFundamentalGroupHomInducedBy_map (laumonModelPr₁ k ≫ inv e) wm)).comp_baseChange
        (isEtaleFundamentalGroupHomInducedBy_basePointHom_id t₀)
  have h₂ := (isEtaleFundamentalGroupHomInducedBy_map (laumonFamilyPr₁ k') z).comp_baseChange
    (isEtaleFundamentalGroupHomInducedBy_map_cast _ _ hz)
  obtain ⟨γ, hγ⟩ := h₂.isInnerConjugate_of_eq h₁ (by
    rw [Category.comp_id, Category.comp_id, ← Category.assoc, ← Category.assoc,
      laumonParamPlane_comp_laumonModelPr₁])
  exact ⟨γ, hγ⟩

variable [Fintype k] [Fintype k'] {E : Type} [CommRing E]

/-- **The Artin–Schreier character of the family is the character of the model**: for
`ψ' = ψ ∘ Tr_{k'/k}`, the character of `a₀ xⁿ + x t` over `k'` is the character of `a xⁿ + x t`
over `k` read along `φ_t ∘ (a ↦ a₀)_*`. -/
theorem artinSchreierCharacter_laumonModel (n : ℕ) (ψ : AddChar k E)
    (z : GeometricPoint (Spec (.of (Polynomial (Polynomial k')))))
    (pz : (finiteEtaleFiberFunctor z).obj
      (Stacks.ArtinSchreier.cover k' (Polynomial (Polynomial k')) (laumonFourierKernel k' n a)))
    (wm : GeometricPoint (Spec (.of (Polynomial (Polynomial (Polynomial k))))))
    (pm : (finiteEtaleFiberFunctor wm).obj
      (Stacks.ArtinSchreier.cover k (Polynomial (Polynomial (Polynomial k)))
        (laumonModelKernel k n)))
    (t : finiteEtaleFiberFunctor wm ≅ finiteEtaleFiberFunctor (z.map (Spec.map (CommRingCat.ofHom
      (mapRingHom (mapRingHom (eval₂RingHom (algebraMap k k') a)))))))
    (γ : EtaleFundamentalGroup (Spec (.of (Polynomial (Polynomial k')))) z) :
    Stacks.ArtinSchreier.artinSchreierCharacter k' (Polynomial (Polynomial k'))
        (laumonFourierKernel k' n a) (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom)
        z pz γ =
      Stacks.ArtinSchreier.artinSchreierCharacter k (Polynomial (Polynomial (Polynomial k)))
        (laumonModelKernel k n) ψ wm pm ((etaleFundamentalGroupBasePointHom t)
          (etaleFundamentalGroupMap (Spec.map (CommRingCat.ofHom
            (mapRingHom (mapRingHom (eval₂RingHom (algebraMap k k') a))))) z γ)) := by
  have hΦ₁ := (isEtaleFundamentalGroupHomInducedBy_map (Spec.map (CommRingCat.ofHom
    (mapRingHom (mapRingHom (eval₂RingHom (algebraMap k k') a))))) z).comp_baseChange
      (isEtaleFundamentalGroupHomInducedBy_basePointHom_id t)
  rw [Category.comp_id] at hΦ₁
  exact artinSchreierCharacter_trace_baseChange_eq k k' ψ _ (fun _ => rfl) (laumonModelKernel k n)
    (laumonParamPlaneAlgHom k k' a) _ (laumonParamPlaneAlgHom_laumonModelKernel k k' a n) wm pm z pz
    _ (𝟙 _) (by rw [Category.id_comp]; rfl) hΦ₁ (isEtaleFundamentalGroupHomInducedBy_id z) γ

end FundamentalGroup

end Stacks.EtaleCohomology

end
