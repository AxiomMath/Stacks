module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackProved
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackCechRelation

/-!
# Morphisms of `Complexes_{X/Y}` descend along an fppf covering

In Situation 0DLE the isomorphism presheaves of `Complexes_{X/Y}` are fppf sheaves: the diagonal
is representable by algebraic spaces (Stacks 0DLG,
`AlgebraicGeometry.Space.ComplexesSituation.complexes_hasRepresentableDiagonal_proved`) and an
algebraic space is an fppf sheaf
(`AlgebraicGeometry.Stack.isSheaf_isomPresheaf_of_hasRepresentableDiagonal`). Since
`Complexes_{X/Y}` is fibred in groupoids, this is the statement that morphisms of `Complexes_{X/Y}`
descend: for an object `P` over a test scheme `T`, a morphism of the site `p : Z ⟶ T` which is an
fppf covering on its own, and an object `G`, a morphism `P|_Z ⟶ G` whose two pullbacks to every
pair of maps into `Z` that agree on `T` agree is the restriction of exactly one morphism `P ⟶ G`.

## Main results

* `AlgebraicGeometry.Space.ComplexesSituation.exists_complexesHom_of_descent`: the gluing of
  morphisms.
* `AlgebraicGeometry.Space.ComplexesSituation.complexesHom_ext_of_descent`: the separation.

## References

* [Stacks Project, Tag 0DLG](https://stacks.math.columbia.edu/tag/0DLG)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 0DLH](https://stacks.math.columbia.edu/tag/0DLH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space.ComplexesSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : ComplexesSituation B S hS}

attribute [local instance] complexesCategory

section Slice

variable (P : ComplexesObject D) (E' : derivedModules B S hS (D.space P.T))
  (hE' : D.IsRelativelyPerfect P.T E') (hX' : D.HasNoNegativeFibreExt P.T E')

/-- The presheaf of morphisms from the pullbacks of an object `P` of `Complexes_{X/Y}` to an object
over the same test scheme, lying over the base, is an fppf sheaf on the slice. -/
theorem isSheaf_sliceTest_homOverPresheaf :
    letI : (complexesFunctor D).IsFibered := (complexesFunctor_isFiberedInGroupoids D).isFibered
    Presheaf.IsSheaf ((BigFppfOver.topology B S hS).over P.T.left)
      ((sliceTestLiftFamily P.T P.E P.relativelyPerfect P.noNegativeFibreExt).homOverPresheaf
        (⟨P.T, E', hE', hX'⟩ : ComplexesObject D)) := by
  let : (complexesFunctor D).IsFibered := (complexesFunctor_isFiberedInGroupoids D).isFibered
  have h := Stack.isSheaf_isomPresheaf_of_hasRepresentableDiagonal B S hS
    (CatFiberedInGroupoids.mk (complexesBasedCategory D) (complexesFunctor_isFiberedInGroupoids D))
    D.complexes_hasRepresentableDiagonal_proved P.T.left
    ⟨⟨P.T, P.E, P.relativelyPerfect, P.noNegativeFibreExt⟩, rfl⟩ ⟨⟨P.T, E', hE', hX'⟩, rfl⟩
  exact (Presheaf.isSheaf_of_iso_iff
    (isomPresheafIsoRelIso P.T P.E P.relativelyPerfect P.noNegativeFibreExt E' hE' hX' ≪≫
      relIsoIsoHomOver P.T P.E P.relativelyPerfect P.noNegativeFibreExt E' hE' hX')).1 h

/-- A morphism out of a pullback of `P` over `sliceTestHom` lies over the base. -/
theorem sliceTest_isHomLift_of_base_eq (g : Over P.T.left)
    (φ : ComplexesHom (sliceTestObj P.T P.E P.relativelyPerfect P.noNegativeFibreExt g)
      (⟨P.T, E', hE', hX'⟩ : ComplexesObject D)) (hφ : φ.base = sliceTestHom D P.T g) :
    (complexesFunctor D).IsHomLift g.hom
      (φ : sliceTestObj P.T P.E P.relativelyPerfect P.noNegativeFibreExt g ⟶ _) := by
  obtain ⟨b, f, hf⟩ := φ
  change b = sliceTestHom D P.T g at hφ
  subst hφ
  exact isHomLift_sliceTestHomOf P.T P.E P.relativelyPerfect P.noNegativeFibreExt E' hE' hX' g f hf

/-- A morphism out of a pullback of `P` lying over the base has the base `sliceTestHom`. -/
theorem sliceTest_base_eq_of_isHomLift (g : Over P.T.left)
    (φ : ComplexesHom (sliceTestObj P.T P.E P.relativelyPerfect P.noNegativeFibreExt g)
      (⟨P.T, E', hE', hX'⟩ : ComplexesObject D))
    (hφ : (complexesFunctor D).IsHomLift g.hom
      (φ : sliceTestObj P.T P.E P.relativelyPerfect P.noNegativeFibreExt g ⟶ _)) :
    φ.base = sliceTestHom D P.T g := by
  have hfac := @IsHomLift.fac' _ _ _ _ (complexesFunctor D) _ _ _ _ g.hom φ hφ
  change (φ : ComplexesHom _ _).base.left = 𝟙 _ ≫ g.hom ≫ 𝟙 _ at hfac
  exact CostructuredArrow.hom_ext _ _ (by rw [hfac, Category.id_comp, Category.comp_id]; rfl)

/-- **Morphisms out of the pullbacks of `P` glue along a single fppf covering** `p : Z ⟶ T`:
a morphism out of the pullback to `Z` whose restrictions along every two maps into `Z` agree is
the restriction of exactly one morphism out of the pullback along the identity of `T`. -/
theorem existsUnique_sliceTestHom {Z₀ : BigFppfOver B S hS} (p : Z₀ ⟶ P.T.left)
    (hp : Sieve.ofArrows (fun _ : PUnit.{u + 1} => Z₀) (fun _ => p) ∈
      BigFppfOver.topology B S hS P.T.left)
    (φ : ComplexesHom (sliceTestObj P.T P.E P.relativelyPerfect P.noNegativeFibreExt (Over.mk p))
      (⟨P.T, E', hE', hX'⟩ : ComplexesObject D))
    (hφ : φ.base = sliceTestHom D P.T (Over.mk p))
    (hc : ∀ (W : Over P.T.left) (p₁ p₂ : W ⟶ Over.mk p),
      (sliceTestTrans P.T P.E P.relativelyPerfect P.noNegativeFibreExt p₁).comp φ =
        (sliceTestTrans P.T P.E P.relativelyPerfect P.noNegativeFibreExt p₂).comp φ) :
    ∃ θ : ComplexesHom
        (sliceTestObj P.T P.E P.relativelyPerfect P.noNegativeFibreExt (Over.mk (𝟙 P.T.left)))
        (⟨P.T, E', hE', hX'⟩ : ComplexesObject D),
      θ.base = sliceTestHom D P.T (Over.mk (𝟙 P.T.left)) ∧
      (sliceTestTrans P.T P.E P.relativelyPerfect P.noNegativeFibreExt
          (Over.homMk p (Category.comp_id p) : Over.mk p ⟶ Over.mk (𝟙 P.T.left))).comp θ = φ ∧
      ∀ θ' : ComplexesHom
          (sliceTestObj P.T P.E P.relativelyPerfect P.noNegativeFibreExt (Over.mk (𝟙 P.T.left)))
          (⟨P.T, E', hE', hX'⟩ : ComplexesObject D),
        θ'.base = sliceTestHom D P.T (Over.mk (𝟙 P.T.left)) →
        (sliceTestTrans P.T P.E P.relativelyPerfect P.noNegativeFibreExt
          (Over.homMk p (Category.comp_id p) : Over.mk p ⟶ Over.mk (𝟙 P.T.left))).comp θ' = φ →
        θ' = θ := by
  let : (complexesFunctor D).IsFibered := (complexesFunctor_isFiberedInGroupoids D).isFibered
  let L := sliceTestLiftFamily P.T P.E P.relativelyPerfect P.noNegativeFibreExt
  let F := L.homOverPresheaf (⟨P.T, E', hE', hX'⟩ : ComplexesObject D)
  have hF := isSheaf_sliceTest_homOverPresheaf P E' hE' hX'
  rw [isSheaf_iff_isSheaf_of_type] at hF
  let f : Over.mk p ⟶ Over.mk (𝟙 P.T.left) := Over.homMk p (Category.comp_id p)
  have hcov : Sieve.ofArrows (fun _ : PUnit.{u + 1} => Over.mk p) (fun _ => f) ∈
      ((BigFppfOver.topology B S hS).over P.T.left) (Over.mk (𝟙 P.T.left)) := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    exact hp
  have hsf : Presieve.IsSheafFor F (Presieve.singleton f) := by
    rw [← Presieve.ofArrows_pUnit]
    exact (Presieve.isSheafFor_iff_generate _).2 (hF _ hcov)
  rw [Presieve.isSheafFor_singleton] at hsf
  let x : F.obj (op (Over.mk p)) := ⟨φ, sliceTest_isHomLift_of_base_eq P E' hE' hX' _ φ hφ⟩
  have hx : ∀ {W : Over P.T.left} (p₁ p₂ : W ⟶ Over.mk p), p₁ ≫ f = p₂ ≫ f →
      F.map p₁.op x = F.map p₂.op x := fun p₁ p₂ _ => by
    refine Subtype.ext ?_
    change L.trans p₁ ≫ φ = L.trans p₂ ≫ φ
    rw [sliceTestLiftFamily_trans, sliceTestLiftFamily_trans]
    exact hc _ p₁ p₂
  obtain ⟨y, hy, hyu⟩ := hsf x hx
  have hyφ : (sliceTestTrans P.T P.E P.relativelyPerfect P.noNegativeFibreExt f).comp y.1 = φ := by
    have := congrArg Subtype.val hy
    change L.trans f ≫ y.1 = φ at this
    rwa [sliceTestLiftFamily_trans] at this
  refine ⟨y.1, sliceTest_base_eq_of_isHomLift P E' hE' hX' _ y.1 y.2, hyφ, fun θ' hθ' hθ'φ => ?_⟩
  have e := hyu ⟨θ', sliceTest_isHomLift_of_base_eq P E' hE' hX' _ θ' hθ'⟩ (by
    refine Subtype.ext ?_
    change L.trans f ≫ θ' = φ
    rw [sliceTestLiftFamily_trans]
    exact hθ'φ)
  exact congrArg Subtype.val e

end Slice

section Descent

variable {P G : ComplexesObject D}

/-- `sliceTestLift` along `g` is the restriction morphism of `P` along `sliceTestHom D P.T g`. -/
theorem sliceTestLift_eq (g : Over P.T.left) :
    sliceTestLift P.T P.E P.relativelyPerfect P.noNegativeFibreExt g =
      restrictComplexHom P (sliceTestHom D P.T g) :=
  rfl

/-- The restriction morphism to `P` from its pullback along the identity of its test scheme has a
section. -/
theorem exists_sliceTest_section :
    ∃ σ : ComplexesHom P
        (sliceTestObj P.T P.E P.relativelyPerfect P.noNegativeFibreExt (Over.mk (𝟙 P.T.left))),
      σ.comp (restrictComplexHom P (sliceTestHom D P.T (Over.mk (𝟙 P.T.left)))) =
        ComplexesHom.id P :=
  (exists_complexesHom_lift (restrictComplexHom P (sliceTestHom D P.T (Over.mk (𝟙 P.T.left))))
    (CostructuredArrow.homMk (𝟙 P.T.left) ((congrArg ((schemeSpaceFunctor B S hS).map
      (𝟙 P.T.left) ≫ ·) (CostructuredArrow.w (𝟙 P.T))).trans (CostructuredArrow.w (𝟙 P.T))))
    (ComplexesHom.id P)
    (CostructuredArrow.hom_ext _ _ (Category.id_comp _))).imp fun _ h => h.2

/-- The pullback of `P` along `p` maps to the pullback along the identity compatibly with the
morphisms to `P`. -/
theorem restrictComplexHom_comp_section {Z₀ : BigFppfOver B S hS} (p : Z₀ ⟶ P.T.left)
    (σ : ComplexesHom P
      (sliceTestObj P.T P.E P.relativelyPerfect P.noNegativeFibreExt (Over.mk (𝟙 P.T.left))))
    (hσ : σ.comp (restrictComplexHom P (sliceTestHom D P.T (Over.mk (𝟙 P.T.left)))) =
      ComplexesHom.id P) :
    (restrictComplexHom P (sliceTestHom D P.T (Over.mk p))).comp σ =
      sliceTestTrans P.T P.E P.relativelyPerfect P.noNegativeFibreExt
        (Over.homMk p (Category.comp_id p) : Over.mk p ⟶ Over.mk (𝟙 P.T.left)) := by
  refine complexesHom_cancel_right
    (restrictComplexHom P (sliceTestHom D P.T (Over.mk (𝟙 P.T.left)))) ?_ ?_
  · have hb := congrArg ComplexesHom.base hσ
    refine CostructuredArrow.hom_ext _ _ ?_
    have hl := congrArg CommaMorphism.left hb
    change σ.base.left ≫ 𝟙 P.T.left = 𝟙 P.T.left at hl
    have hl' : σ.base.left = 𝟙 P.T.left := (Category.comp_id _).symm.trans hl
    change p ≫ σ.base.left = p
    exact (congrArg (p ≫ ·) hl').trans (Category.comp_id p)
  · rw [ComplexesHom.assoc, hσ, ComplexesHom.comp_id]
    exact (sliceTestTrans_comp_lift P.T P.E P.relativelyPerfect P.noNegativeFibreExt
      (Over.homMk p (Category.comp_id p) : Over.mk p ⟶ Over.mk (𝟙 P.T.left))).symm

/-- Two transition morphisms into the pullback along `p` agree after restricting to `P`. -/
private theorem sliceTestTrans_comp_restrict_eq {Z₀ : BigFppfOver B S hS} (p : Z₀ ⟶ P.T.left)
    {W : Over P.T.left} (p₁ p₂ : W ⟶ Over.mk p) :
    (sliceTestTrans P.T P.E P.relativelyPerfect P.noNegativeFibreExt p₁).comp
        (restrictComplexHom P (sliceTestHom D P.T (Over.mk p))) =
      (sliceTestTrans P.T P.E P.relativelyPerfect P.noNegativeFibreExt p₂).comp
        (restrictComplexHom P (sliceTestHom D P.T (Over.mk p))) :=
  (sliceTestTrans_comp_lift P.T P.E P.relativelyPerfect P.noNegativeFibreExt p₁).trans
    (sliceTestTrans_comp_lift P.T P.E P.relativelyPerfect P.noNegativeFibreExt p₂).symm

/-- **Morphisms of `Complexes_{X/Y}` descend along a single fppf covering.** Let `P` be an object
over a test scheme `T`, `p : Z ⟶ T` a morphism of the site whose singleton sieve is an fppf
covering, and `Ψ' : P|_Z ⟶ G` a morphism over `p ≫ b` whose restrictions along every two
morphisms into `P|_Z` agreeing on `P` agree. Then `Ψ'` is the restriction of a morphism
`P ⟶ G` over `b`. -/
theorem exists_complexesHom_of_descent (b : P.T ⟶ G.T) {Z₀ : BigFppfOver B S hS}
    (p : Z₀ ⟶ P.T.left)
    (hp : Sieve.ofArrows (fun _ : PUnit.{u + 1} => Z₀) (fun _ => p) ∈
      BigFppfOver.topology B S hS P.T.left)
    (Ψ' : ComplexesHom (restrictComplex P (sliceTestHom D P.T (Over.mk p))) G)
    (hΨ' : Ψ'.base = sliceTestHom D P.T (Over.mk p) ≫ b)
    (hc : ∀ (A : ComplexesObject D)
      (h₁ h₂ : ComplexesHom A (restrictComplex P (sliceTestHom D P.T (Over.mk p)))),
      h₁.comp (restrictComplexHom P (sliceTestHom D P.T (Over.mk p))) =
        h₂.comp (restrictComplexHom P (sliceTestHom D P.T (Over.mk p))) →
      h₁.comp Ψ' = h₂.comp Ψ') :
    ∃ Ψ : ComplexesHom P G, Ψ.base = b ∧
      (restrictComplexHom P (sliceTestHom D P.T (Over.mk p))).comp Ψ = Ψ' := by
  obtain ⟨φ, hφb, hφ⟩ := exists_complexesHom_lift (restrictComplexHom G b)
    (sliceTestHom D P.T (Over.mk p)) Ψ' hΨ'.symm
  have hc' : ∀ (W : Over P.T.left) (p₁ p₂ : W ⟶ Over.mk p),
      (sliceTestTrans P.T P.E P.relativelyPerfect P.noNegativeFibreExt p₁).comp φ =
        (sliceTestTrans P.T P.E P.relativelyPerfect P.noNegativeFibreExt p₂).comp φ := by
    intro W p₁ p₂
    have e := sliceTestTrans_comp_restrict_eq p p₁ p₂
    refine complexesHom_cancel_right (restrictComplexHom G b) ?_ ?_
    · have hb := congrArg ComplexesHom.base e
      change (sliceTestTrans P.T P.E P.relativelyPerfect P.noNegativeFibreExt p₁).base ≫ φ.base =
        (sliceTestTrans P.T P.E P.relativelyPerfect P.noNegativeFibreExt p₂).base ≫ φ.base
      rwa [hφb]
    · rw [ComplexesHom.assoc, ComplexesHom.assoc, hφ]
      exact hc _ _ _ e
  obtain ⟨θ, hθb, hθ, -⟩ := existsUnique_sliceTestHom P (restrictComplex G b).E
    (restrictComplex G b).relativelyPerfect (restrictComplex G b).noNegativeFibreExt p hp φ hφb hc'
  obtain ⟨σ, hσ⟩ := exists_sliceTest_section (P := P)
  refine ⟨σ.comp (θ.comp (restrictComplexHom G b)), ?_, ?_⟩
  · have hb := congrArg ComplexesHom.base hσ
    change σ.base ≫ θ.base ≫ b = b
    change σ.base ≫ sliceTestHom D P.T (Over.mk (𝟙 P.T.left)) = 𝟙 P.T at hb
    rw [hθb, ← Category.assoc, hb, Category.id_comp]
  · rw [← ComplexesHom.assoc, restrictComplexHom_comp_section p σ hσ, ← ComplexesHom.assoc, hθ,
      hφ]

/-- **Morphisms of `Complexes_{X/Y}` are determined by their restrictions along a single fppf
covering.** -/
theorem complexesHom_ext_of_descent {Ψ₁ Ψ₂ : ComplexesHom P G} (hb : Ψ₁.base = Ψ₂.base)
    {Z₀ : BigFppfOver B S hS} (p : Z₀ ⟶ P.T.left)
    (hp : Sieve.ofArrows (fun _ : PUnit.{u + 1} => Z₀) (fun _ => p) ∈
      BigFppfOver.topology B S hS P.T.left)
    (h : (restrictComplexHom P (sliceTestHom D P.T (Over.mk p))).comp Ψ₁ =
      (restrictComplexHom P (sliceTestHom D P.T (Over.mk p))).comp Ψ₂) : Ψ₁ = Ψ₂ := by
  obtain ⟨χ₁, hχ₁b, hχ₁⟩ := exists_complexesHom_lift (restrictComplexHom G Ψ₁.base) (𝟙 P.T) Ψ₁
    (Category.id_comp _)
  obtain ⟨χ₂, hχ₂b, hχ₂⟩ := exists_complexesHom_lift (restrictComplexHom G Ψ₁.base) (𝟙 P.T) Ψ₂
    ((Category.id_comp _).trans hb)
  let ρ := restrictComplexHom P (sliceTestHom D P.T (Over.mk p))
  let lift₁ := restrictComplexHom P (sliceTestHom D P.T (Over.mk (𝟙 P.T.left)))
  have hρχ : ρ.comp χ₁ = ρ.comp χ₂ := by
    refine complexesHom_cancel_right (restrictComplexHom G Ψ₁.base) ?_ ?_
    · change ρ.base ≫ χ₁.base = ρ.base ≫ χ₂.base
      rw [hχ₁b, hχ₂b]
    · rw [ComplexesHom.assoc, ComplexesHom.assoc, hχ₁, hχ₂, h]
  have hbase : ∀ (g : Over P.T.left) (χ : ComplexesHom P (restrictComplex G Ψ₁.base)),
      χ.base = 𝟙 P.T →
      ((restrictComplexHom P (sliceTestHom D P.T g)).comp χ).base = sliceTestHom D P.T g :=
    fun g χ hχ => by
    change _ ≫ χ.base = _
    rw [hχ, Category.comp_id]
  have hcomp : ∀ χ : ComplexesHom P (restrictComplex G Ψ₁.base),
      (sliceTestTrans P.T P.E P.relativelyPerfect P.noNegativeFibreExt
        (Over.homMk p (Category.comp_id p) : Over.mk p ⟶ Over.mk (𝟙 P.T.left))).comp
          (lift₁.comp χ) = ρ.comp χ := fun χ => by
    rw [← ComplexesHom.assoc]
    exact congrArg (·.comp χ) (sliceTestTrans_comp_lift P.T P.E P.relativelyPerfect
      P.noNegativeFibreExt (Over.homMk p (Category.comp_id p) : Over.mk p ⟶ Over.mk (𝟙 P.T.left)))
  have hc' : ∀ (W : Over P.T.left) (p₁ p₂ : W ⟶ Over.mk p),
      (sliceTestTrans P.T P.E P.relativelyPerfect P.noNegativeFibreExt p₁).comp (ρ.comp χ₁) =
        (sliceTestTrans P.T P.E P.relativelyPerfect P.noNegativeFibreExt p₂).comp (ρ.comp χ₁) := by
    intro W p₁ p₂
    rw [← ComplexesHom.assoc, ← ComplexesHom.assoc]
    exact congrArg (·.comp χ₁) (sliceTestTrans_comp_restrict_eq p p₁ p₂)
  obtain ⟨θ, -, -, hθu⟩ := existsUnique_sliceTestHom P (restrictComplex G Ψ₁.base).E
    (restrictComplex G Ψ₁.base).relativelyPerfect (restrictComplex G Ψ₁.base).noNegativeFibreExt
    p hp (ρ.comp χ₁) (hbase _ χ₁ hχ₁b) hc'
  have e₁ := hθu (lift₁.comp χ₁) (hbase _ χ₁ hχ₁b) (hcomp χ₁)
  have e₂ := hθu (lift₁.comp χ₂) (hbase _ χ₂ hχ₂b) ((hcomp χ₂).trans hρχ.symm)
  obtain ⟨σ, hσ⟩ := exists_sliceTest_section (P := P)
  have hχ : χ₁ = χ₂ := by
    have := congrArg (σ.comp ·) (e₁.trans e₂.symm)
    simp only [← ComplexesHom.assoc] at this
    rwa [hσ, ComplexesHom.id_comp, ComplexesHom.id_comp] at this
  rw [← hχ₁, ← hχ₂, hχ]

end Descent

end AlgebraicGeometry.Space.ComplexesSituation

end
