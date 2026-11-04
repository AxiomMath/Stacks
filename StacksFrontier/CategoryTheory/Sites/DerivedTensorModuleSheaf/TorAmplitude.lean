module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.DerivedChangeOfRings
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.IdealPowerTriangles

/-!
# Tor amplitude of complexes of sheaves of modules over a ring

Let `(C, J)` be a site and `Λ` a commutative ring. An object `K` of the derived category
`D(C, Λ)` of sheaves of `Λ`-modules has *Tor amplitude in* a set `S` of degrees if
`Hⁱ(K ⊗_Λ^L F) = 0` for every sheaf of `Λ`-modules `F` and every `i ∉ S`. Tor amplitude in
`[a, b]` and in `[a, ∞)` (Stacks 08FZ) are the cases `S = Set.Icc a b` and `S = Set.Ici a`.

Let `I ⊆ Λ` be a finitely generated ideal and `Kₙ = K ⊗_Λ^L Λ/Iⁿ`, an object of `D(C, Λ/Iⁿ)`. If
`K₁` has Tor amplitude in `S`, then so has `Kₙ` for every `n`: this is Stacks 0942 for the
constant sheaf of rings `Λ`.

## Main definitions

* `Stacks.ModuleSheaf.HasTorAmplitude`: Tor amplitude in a set of degrees.
* `Stacks.ModuleSheaf.ofIsTorsionBySet`: a sheaf of `Λ`-modules whose sections are killed by `I`,
  regarded as a sheaf of `Λ/I`-modules.

## Main results

* `Stacks.ModuleSheaf.HasTorAmplitude.isGE`: an object with Tor amplitude in `[a, ∞)` lies in
  degrees `≥ a`.
* `CategoryTheory.Linear.exists_shortExact_smul_id_eq_zero`: in a `Λ`-linear abelian category,
  an object killed by `Iⁿ⁺¹` is an extension of an object killed by `Iⁿ` by one killed by `I`.
* `Stacks.ModuleSheaf.essImage_restrictScalars_of_smul_id_eq_zero`: a sheaf of `Λ`-modules
  killed by `I` is a sheaf of `Λ/I`-modules read over `Λ`.
* `Stacks.ModuleSheaf.isZero_homology_tensor_of_smul_id_eq_zero`: the dévissage, from the
  sheaves killed by `I` to the sheaves killed by `Iⁿ`.
* `Stacks.ModuleSheaf.HasTorAmplitude.isZero_homology_single_tensor_of_smul_id_eq_zero`: if
  `K ⊗_Λ^L Λ/I` has Tor amplitude in `S`, then `Hⁱ(G ⊗_Λ^L K) = 0` off `S` for every sheaf `G`
  killed by a power of `I`.
* `Stacks.ModuleSheaf.HasTorAmplitude.derivedExtendScalars_pow`: Tor amplitude of `Kₙ` from
  Tor amplitude of `K₁`.

## References

* [Stacks Project, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
* [Stacks Project, Tag 0942](https://stacks.math.columbia.edu/tag/0942)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe t t' t'' w v u

/-! ### Objects of a linear category killed by an ideal -/

namespace CategoryTheory.Linear

variable {R : Type*} [CommRing R] {𝒜 : Type*} [Category 𝒜]

section Preadditive

variable [Preadditive 𝒜] [Linear R 𝒜]

/-- An object killed by the elements of a set is killed by the ideal they generate. -/
theorem smul_id_eq_zero_of_mem_span {s : Set R} {X : 𝒜} (hX : ∀ x ∈ s, x • 𝟙 X = 0) {x : R}
    (hx : x ∈ Ideal.span s) : x • 𝟙 X = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact hX x hx
  | zero => exact zero_smul R _
  | add x y _ _ hx hy => rw [add_smul, hx, hy, add_zero]
  | smul r x _ hx => rw [smul_eq_mul, mul_smul, hx, smul_zero]

end Preadditive

variable [Abelian 𝒜] [Linear R 𝒜]

/-- **An object killed by `Iⁿ⁺¹` is an extension of an object killed by `Iⁿ` by an object killed
by `I`**, for a finitely generated ideal `I`. -/
theorem exists_shortExact_smul_id_eq_zero {I : Ideal R} (hI : I.FG) {n : ℕ} {X : 𝒜}
    (hX : ∀ x ∈ I ^ (n + 1), x • 𝟙 X = 0) :
    ∃ S : ShortComplex 𝒜, S.ShortExact ∧ S.X₂ = X ∧ (∀ x ∈ I, x • 𝟙 S.X₁ = 0) ∧
      ∀ x ∈ I ^ n, x • 𝟙 S.X₃ = 0 := by
  obtain ⟨s, hs⟩ := hI
  let φ : X ⟶ ∏ᶜ fun x : s => X := Pi.lift fun x => (x : R) • 𝟙 X
  refine ⟨ShortComplex.mk (kernel.ι φ) (cokernel.π (kernel.ι φ)) (cokernel.condition _),
    ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _))
      inferInstance inferInstance, rfl, ?_, ?_⟩
  · rw [← hs]
    refine fun x hx => smul_id_eq_zero_of_mem_span (fun x hx => ?_) hx
    refine (cancel_mono (kernel.ι φ)).1 ?_
    have h : kernel.ι φ ≫ φ ≫ Pi.π (fun _ : s => X) ⟨x, hx⟩ = 0 := by
      rw [← Category.assoc, kernel.condition, zero_comp]
    rw [Pi.lift_π, Linear.comp_smul, Category.comp_id] at h
    rw [Linear.smul_comp, Category.id_comp, h, zero_comp]
  · intro y hy
    have hφ : (y • 𝟙 X) ≫ φ = 0 := Pi.hom_ext _ _ fun x => by
      rw [Category.assoc, Pi.lift_π, Linear.comp_smul, Category.comp_id, smul_smul, zero_comp]
      exact hX _ (by
        rw [mul_comm, pow_succ]
        exact Ideal.mul_mem_mul hy (hs ▸ Ideal.subset_span x.2))
    refine (cancel_epi (cokernel.π (kernel.ι φ))).1 ?_
    dsimp
    rw [Linear.comp_smul, Category.comp_id, comp_zero, ← Category.id_comp (cokernel.π _),
      ← Linear.smul_comp, ← kernel.lift_ι φ _ hφ, Category.assoc, cokernel.condition, comp_zero]

end CategoryTheory.Linear

namespace Stacks.ModuleSheaf

attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory monoidalClosed
  CochainComplex.braidedCategory derivedMonoidal derivedSymmetric

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {Λ : Type w} [CommRing Λ] [UnivLE.{max u v, w}]

/-! ### Tor amplitude -/

section TorAmplitude

variable [HasDerivedCategory.{t} (Sheaf J (ModuleCat.{w} Λ))]

/-- An object `K` of `D(C, Λ)` has *Tor amplitude in* the set of degrees `S` if, for every sheaf
of `Λ`-modules `F`, the derived tensor product `K ⊗_Λ^L F` has vanishing cohomology sheaves in
the degrees outside `S`. Tor amplitude in `[a, b]`, resp. in `[a, ∞)`, is the case
`S = Set.Icc a b`, resp. `S = Set.Ici a`. -/
def HasTorAmplitude (K : DerivedCategory (Sheaf J (ModuleCat.{w} Λ))) (S : Set ℤ) : Prop :=
  ∀ (F : Sheaf J (ModuleCat.{w} Λ)) (i : ℤ), i ∉ S →
    IsZero ((DerivedCategory.homologyFunctor _ i).obj
      (K ⊗ (DerivedCategory.singleFunctor _ 0).obj F))

variable {K K' : DerivedCategory (Sheaf J (ModuleCat.{w} Λ))} {S S' : Set ℤ}

/-- Tor amplitude transports along an isomorphism. -/
theorem HasTorAmplitude.of_iso (e : K ≅ K') (h : HasTorAmplitude K S) : HasTorAmplitude K' S :=
  fun F i hi => (h F i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso
    (e.symm ⊗ᵢ Iso.refl _))

/-- Tor amplitude in `S` is Tor amplitude in every larger set of degrees. -/
theorem HasTorAmplitude.mono (hS : S ⊆ S') (h : HasTorAmplitude K S) : HasTorAmplitude K S' :=
  fun F i hi => h F i fun h' => hi (hS h')

/-- Outside its Tor amplitude, an object has vanishing cohomology. -/
theorem HasTorAmplitude.isZero_homology (h : HasTorAmplitude K S) {i : ℤ} (hi : i ∉ S) :
    IsZero ((DerivedCategory.homologyFunctor _ i).obj K) := by
  refine (h (𝟙_ _) i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso ?_)
  exact (ρ_ K).symm ≪≫ (Iso.refl K ⊗ᵢ
    (CochainComplex.KFlatMonoidal.derivedUnitIso _ (exists_kFlat_quasiIso (J := J) (Λ := Λ)) ≪≫
      (DerivedCategory.singleFunctorIsoCompQ _ 0).symm.app _))

/-- **An object with Tor amplitude in `[a, ∞)` lies in degrees `≥ a`.** -/
theorem HasTorAmplitude.isGE {a : ℤ} (h : HasTorAmplitude K (Set.Ici a)) : K.IsGE a :=
  (DerivedCategory.isGE_iff _ _).2 fun _ hi => h.isZero_homology (by simpa using hi)

/-- **An object with Tor amplitude in `(-∞, b]` lies in degrees `≤ b`.** -/
theorem HasTorAmplitude.isLE {b : ℤ} (h : HasTorAmplitude K (Set.Iic b)) : K.IsLE b :=
  (DerivedCategory.isLE_iff _ _).2 fun _ hi => h.isZero_homology (by simpa using hi)

/-- An object with Tor amplitude in `[a, b]` lies in degrees `[a, b]`. -/
theorem HasTorAmplitude.isGE_isLE {a b : ℤ} (h : HasTorAmplitude K (Set.Icc a b)) :
    K.IsGE a ∧ K.IsLE b :=
  ⟨(h.mono Set.Icc_subset_Ici_self).isGE, (h.mono Set.Icc_subset_Iic_self).isLE⟩

end TorAmplitude

/-! ### Sheaves of modules killed by an ideal -/

section Torsion

variable (I : Ideal Λ)

omit [UnivLE.{max u v, w}] in
/-- The sections of a sheaf of `Λ`-modules killed by `I` are killed by `I`. -/
theorem isTorsionBySet_of_smul_id_eq_zero {G : Sheaf J (ModuleCat.{w} Λ)}
    (hG : ∀ x ∈ I, x • 𝟙 G = 0) (U : Cᵒᵖ) : Module.IsTorsionBySet Λ (G.obj.obj U) I :=
  fun s x => congrArg (fun φ : G ⟶ G => (φ.hom.app U).hom s) (hG x x.2)

omit [UnivLE.{max u v, w}] in
variable {I} in
/-- A sheaf read over `Λ` along `f : Λ →+* S` is killed by the kernel of `f`. -/
theorem smul_id_restrictScalars_eq_zero {S : Type w} [CommRing S] (f : Λ →+* S)
    (F : Sheaf J (ModuleCat.{w} S)) {x : Λ} (hx : f x = 0) :
    x • 𝟙 ((restrictScalars J f).obj F) = 0 := by
  ext U s
  exact (congrArg (fun c : S => @HSMul.hSMul S (F.obj.obj U) (F.obj.obj U) _ c s) hx).trans
    (zero_smul S (show F.obj.obj U from s))

/-- A presheaf of `Λ`-modules whose sections are killed by `I`, as a presheaf of `Λ/I`-modules. -/
def presheafOfIsTorsionBySet (P : Cᵒᵖ ⥤ ModuleCat.{w} Λ)
    (hP : ∀ U, Module.IsTorsionBySet Λ (P.obj U) I) : Cᵒᵖ ⥤ ModuleCat.{w} (Λ ⧸ I) where
  obj U := letI := (hP U).module; ModuleCat.of (Λ ⧸ I) (P.obj U)
  map {U V} φ := letI := (hP U).module; letI := (hP V).module; ModuleCat.ofHom
    { toFun := P.map φ
      map_add' := map_add (P.map φ).hom
      map_smul' := fun c s => by
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
        rw [RingHom.id_apply, Module.IsTorsionBySet.mk_smul (hP U),
          Module.IsTorsionBySet.mk_smul (hP V)]
        exact (P.map φ).hom.map_smul r s }
  map_id U := by
    ext s
    exact congrArg (fun g => g.hom s) (P.map_id U)
  map_comp φ ψ := by
    ext s
    exact congrArg (fun g => g.hom s) (P.map_comp φ ψ)

/-- Read back over `Λ`, `Stacks.ModuleSheaf.presheafOfIsTorsionBySet` is the presheaf it was
built from. -/
def presheafOfIsTorsionBySetCompRestrictScalarsIso (P : Cᵒᵖ ⥤ ModuleCat.{w} Λ)
    (hP : ∀ U, Module.IsTorsionBySet Λ (P.obj U) I) :
    presheafOfIsTorsionBySet I P hP ⋙ ModuleCat.restrictScalars.{w} (Ideal.Quotient.mk I) ≅ P :=
  NatIso.ofComponents (fun U =>
    show (ModuleCat.restrictScalars.{w} (Ideal.Quotient.mk I)).obj
        ((presheafOfIsTorsionBySet I P hP).obj U) ≅ P.obj U from
    LinearEquiv.toModuleIso (m₁ := ((ModuleCat.restrictScalars.{w} (Ideal.Quotient.mk I)).obj
        ((presheafOfIsTorsionBySet I P hP).obj U)).isModule)
      { toFun := fun s => s
        invFun := fun s => s
        map_add' := fun _ _ => rfl
        map_smul' := fun r s => Module.IsTorsionBySet.mk_smul (hP U) r s
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }) fun _ => rfl

/-- **A sheaf of `Λ`-modules whose sections are killed by `I`, as a sheaf of `Λ/I`-modules.** -/
def ofIsTorsionBySet (G : Sheaf J (ModuleCat.{w} Λ))
    (hG : ∀ U, Module.IsTorsionBySet Λ (G.obj.obj U) I) : Sheaf J (ModuleCat.{w} (Λ ⧸ I)) :=
  ⟨presheafOfIsTorsionBySet I G.obj hG, by
    have : HasLimitsOfSize.{v, max v u} (ModuleCat.{w} (Λ ⧸ I)) :=
      ModuleCat.hasLimitsOfSize.{v, max v u, w}
    exact (Presheaf.isSheaf_iff_isSheaf_comp J _
      (ModuleCat.restrictScalars.{w} (Ideal.Quotient.mk I))).2
      ((Presheaf.isSheaf_of_iso_iff (presheafOfIsTorsionBySetCompRestrictScalarsIso I G.obj hG)).2
        G.property)⟩

/-- Read back over `Λ`, `Stacks.ModuleSheaf.ofIsTorsionBySet` is the sheaf it was built from. -/
def restrictScalarsOfIsTorsionBySetIso (G : Sheaf J (ModuleCat.{w} Λ))
    (hG : ∀ U, Module.IsTorsionBySet Λ (G.obj.obj U) I) :
    (restrictScalars J (Ideal.Quotient.mk I)).obj (ofIsTorsionBySet I G hG) ≅ G :=
  (fullyFaithfulSheafToPresheaf J _).preimageIso
    (presheafOfIsTorsionBySetCompRestrictScalarsIso I G.obj hG)

/-- **A sheaf of `Λ`-modules killed by `I` is a sheaf of `Λ/I`-modules read over `Λ`.** -/
theorem essImage_restrictScalars_of_smul_id_eq_zero (G : Sheaf J (ModuleCat.{w} Λ))
    (hG : ∀ x ∈ I, x • 𝟙 G = 0) : (restrictScalars J (Ideal.Quotient.mk I)).essImage G :=
  ⟨_, ⟨restrictScalarsOfIsTorsionBySetIso I G (isTorsionBySet_of_smul_id_eq_zero I hG)⟩⟩

end Torsion

/-! ### The dévissage -/

section Devissage

variable [HasDerivedCategory.{t} (Sheaf J (ModuleCat.{w} Λ))] {I : Ideal Λ}

/-- **The dévissage from sheaves killed by `I` to sheaves killed by `Iⁿ`.** If the cohomology
sheaf in degree `i` of `G ⊗_Λ^L K` vanishes for every sheaf of `Λ`-modules `G` killed by `I`,
then it vanishes for every sheaf killed by a power of `I`. -/
theorem isZero_homology_tensor_of_smul_id_eq_zero (hI : I.FG)
    (K : DerivedCategory (Sheaf J (ModuleCat.{w} Λ))) (i : ℤ)
    (h : ∀ G : Sheaf J (ModuleCat.{w} Λ), (∀ x ∈ I, x • 𝟙 G = 0) →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj
        ((DerivedCategory.singleFunctor _ 0).obj G ⊗ K)))
    (n : ℕ) (G : Sheaf J (ModuleCat.{w} Λ)) (hG : ∀ x ∈ I ^ n, x • 𝟙 G = 0) :
    IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((DerivedCategory.singleFunctor _ 0).obj G ⊗ K)) := by
  obtain ⟨_, _⟩ := exists_commShift_isTriangulated_tensorRight J Λ K
  induction n generalizing G with
  | zero =>
    have hz : IsZero G := by
      rw [IsZero.iff_id_eq_zero, ← one_smul Λ (𝟙 G)]
      exact hG 1 (by simp)
    exact (DerivedCategory.homologyFunctor _ i).map_isZero
      ((tensorRight K).map_isZero ((DerivedCategory.singleFunctor _ 0).map_isZero hz))
  | succ n ih =>
    obtain ⟨S, hS, rfl, h₁, h₃⟩ := Linear.exists_shortExact_smul_id_eq_zero hI hG
    obtain ⟨_, _, _, hT⟩ :=
      Stacks.ConstantSheaf.exists_distTriang_map_singleTriangle (tensorRight K) S hS
    exact ((DerivedCategory.homologyFunctor _ 0).homologySequence_exact₂ _ hT i).isZero_X₂
      ((h _ h₁).eq_of_src _ _) ((ih _ h₃).eq_of_tgt _ _)

variable {S : Type w} [CommRing S] [HasDerivedCategory.{t'} (Sheaf J (ModuleCat.{w} S))]

/-- **The cohomology of `F ⊗_S^L (K ⊗_Λ^L S)`, read over `Λ`, is that of `F ⊗_Λ^L K`**, in each
degree `i`, for a sheaf of `S`-modules `F`. -/
theorem nonempty_restrictScalars_homology_tensor_derivedExtendScalars_iso (f : Λ →+* S)
    (F : Sheaf J (ModuleCat.{w} S)) (K : DerivedCategory (Sheaf J (ModuleCat.{w} Λ))) (i : ℤ) :
    Nonempty ((restrictScalars J f).obj ((DerivedCategory.homologyFunctor _ i).obj
        ((DerivedCategory.singleFunctor _ 0).obj F ⊗ (derivedExtendScalars J f).obj K)) ≅
      (DerivedCategory.homologyFunctor _ i).obj
        ((DerivedCategory.singleFunctor _ 0).obj ((restrictScalars J f).obj F) ⊗ K)) := by
  let R := restrictScalars J f
  obtain ⟨e⟩ := nonempty_restrictScalars_tensor_derivedExtendScalars_iso f
    ((DerivedCategory.singleFunctor _ 0).obj F) K
  exact ⟨((R.mapDerivedCategoryHomologyIso i).app _).symm ≪≫
    (DerivedCategory.homologyFunctor _ i).mapIso
      (e ≪≫ ((R.mapDerivedCategorySingleFunctor 0).app F ⊗ᵢ Iso.refl K))⟩

omit [UnivLE.{max u v, w}] [HasDerivedCategory.{t} (Sheaf J (ModuleCat.{w} Λ))]
  [HasDerivedCategory.{t'} (Sheaf J (ModuleCat.{w} S))] in
/-- A sheaf of `S`-modules whose restriction of scalars along `f` is zero is zero. -/
theorem isZero_of_isZero_restrictScalars_obj (f : Λ →+* S) {F : Sheaf J (ModuleCat.{w} S)}
    (hF : IsZero ((restrictScalars J f).obj F)) : IsZero F := by
  rw [IsZero.iff_id_eq_zero] at hF ⊢
  exact (restrictScalars J f).map_injective
    (by rw [CategoryTheory.Functor.map_id, hF, CategoryTheory.Functor.map_zero])

/-- Commuting the factors of a derived tensor product preserves vanishing of cohomology. -/
private theorem isZero_homology_tensor_comm {X Y : DerivedCategory (Sheaf J (ModuleCat.{w} Λ))}
    {i : ℤ} (h : IsZero ((DerivedCategory.homologyFunctor _ i).obj (X ⊗ Y))) :
    IsZero ((DerivedCategory.homologyFunctor _ i).obj (Y ⊗ X)) :=
  h.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso (β_ _ _))

variable (I) in
/-- **Vanishing off the Tor amplitude of the reduction, against every sheaf killed by a power of
`I`.** If `K ⊗_Λ^L Λ/I` has Tor amplitude in `S` as an object of `D(C, Λ/I)`, then
`Hⁱ(G ⊗_Λ^L K) = 0` for every `i ∉ S` and every sheaf of `Λ`-modules `G` killed by some power
`Iⁿ`. -/
theorem HasTorAmplitude.isZero_homology_single_tensor_of_smul_id_eq_zero
    [HasDerivedCategory.{t'} (Sheaf J (ModuleCat.{w} (Λ ⧸ I)))] (hI : I.FG)
    {K : DerivedCategory (Sheaf J (ModuleCat.{w} Λ))} {S : Set ℤ}
    (h : HasTorAmplitude ((derivedExtendScalars J (Ideal.Quotient.mk I)).obj K) S) (n : ℕ)
    (G : Sheaf J (ModuleCat.{w} Λ)) (hG : ∀ x ∈ I ^ n, x • 𝟙 G = 0) {i : ℤ} (hi : i ∉ S) :
    IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((DerivedCategory.singleFunctor _ 0).obj G ⊗ K)) := by
  refine isZero_homology_tensor_of_smul_id_eq_zero hI K i (fun G hG => ?_) n G hG
  obtain ⟨G', ⟨eG⟩⟩ := essImage_restrictScalars_of_smul_id_eq_zero I G hG
  obtain ⟨e'⟩ := nonempty_restrictScalars_homology_tensor_derivedExtendScalars_iso
    (Ideal.Quotient.mk I) G' K i
  refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor _ i).mapIso
    ((DerivedCategory.singleFunctor _ 0).mapIso eG.symm ⊗ᵢ Iso.refl K) ≪≫ e'.symm)
  exact (restrictScalars J _).map_isZero (isZero_homology_tensor_comm (h G' i hi))

variable (I) [HasDerivedCategory.{t'} (Sheaf J (ModuleCat.{w} (Λ ⧸ I)))]
  [∀ n : ℕ, HasDerivedCategory.{t''} (Sheaf J (ModuleCat.{w} (Λ ⧸ I ^ n)))]

/-- **Tor amplitude modulo every power of a finitely generated ideal.** If `K ⊗_Λ^L Λ/I` has Tor
amplitude in `S` as an object of `D(C, Λ/I)`, then `K ⊗_Λ^L Λ/Iⁿ` has Tor amplitude in `S` as an
object of `D(C, Λ/Iⁿ)`, for every `n`. -/
theorem HasTorAmplitude.derivedExtendScalars_pow (hI : I.FG)
    {K : DerivedCategory (Sheaf J (ModuleCat.{w} Λ))} {S : Set ℤ}
    (h : HasTorAmplitude ((derivedExtendScalars J (Ideal.Quotient.mk I)).obj K) S) (n : ℕ) :
    HasTorAmplitude ((derivedExtendScalars J (Ideal.Quotient.mk (I ^ n))).obj K) S := by
  intro F i hi
  refine isZero_homology_tensor_comm ?_
  refine isZero_of_isZero_restrictScalars_obj (Ideal.Quotient.mk (I ^ n)) ?_
  obtain ⟨e⟩ := nonempty_restrictScalars_homology_tensor_derivedExtendScalars_iso
    (Ideal.Quotient.mk (I ^ n)) F K i
  exact (h.isZero_homology_single_tensor_of_smul_id_eq_zero I hI n _
    (fun x hx => smul_id_restrictScalars_eq_zero _ F (Ideal.Quotient.eq_zero_iff_mem.2 hx))
    hi).of_iso e

end Devissage

end Stacks.ModuleSheaf

end
