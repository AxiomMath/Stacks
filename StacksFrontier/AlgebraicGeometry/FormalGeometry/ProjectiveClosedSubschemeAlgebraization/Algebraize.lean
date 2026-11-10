module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ProjectiveClosedSubschemeAlgebraization.QuotientSystem
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.AffineSections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.AdicQuotientDerivedLimit
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.SchemeTheoretic
public import StacksFrontier.AlgebraicGeometry.Cohomology.LocallyNoetherian.StructureSheafCoherent
public import StacksFrontier.AlgebraicGeometry.CoherentSubquotients.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.InjectiveQcoh.IdealPowerQuasicoherent

/-!
# Algebraizing a formal closed subscheme when completion is an equivalence

Let `X` be a locally Noetherian scheme and `𝓘` a quasi-coherent ideal sheaf on `X` such that the
completion functor `Coh(𝒪_X) ⥤ Coh(X, 𝓘)` of Stacks 0880 is an equivalence. Then every decreasing
sequence of quasi-coherent ideal sheaves `(Jₙ)` with `𝓘 ^ (n + 1) ⊆ Jₙ` and
`Jₙ = 𝓘 ^ (n + 1) + J_{n+1}` — a formal closed subscheme of the completion of `X` along `𝓘` — is
cut out by a single quasi-coherent ideal sheaf `K`: `Jₙ = K + 𝓘 ^ (n + 1)` for every `n`.

The proof is the argument of [Stacks, Tag 0899]. The structure sheaves `𝒪_X / Jₙ` form a
coherent adic system (`Stacks.Algebraization.isCoherentAdicSystem_idealQuotientSystem`), which by
essential surjectivity is the completion of a coherent module `𝒢`. By fullness the projections
`𝒪_X / 𝓘 ^ (n + 1) ⟶ 𝒪_X / Jₙ` come from a map `φ : 𝒪_X ⟶ 𝒢`; it is an epimorphism because its
completion is one and a faithful functor reflects epimorphisms, applied first to the completion
functor and then to the inclusion of coherent modules, whose cokernel stays coherent. The ideal
sheaf `K` is then the scheme-theoretic support of `𝒢`, the annihilator of `𝒢 = 𝒪_X / K`, and the
identity `Jₙ = K + 𝓘 ^ (n + 1)` is checked on the sections over an affine open, where it is the
statement that `(R / K) / 𝓘 ^ (n + 1) = R / Jₙ` compatibly with the projections from `R`.

## Main results

* `Stacks.Algebraization.exists_idealSheaf_sup_eq_of_isEquivalence` — the algebraization of a
  formal closed subscheme.
* `Stacks.Algebraization.eq_schemeTheoreticSupport_sup_of_epi` — the affine-local identification
  of the ideal sheaf of a quotient of `𝒪_X` modulo `𝓘 ^ m`.
* `Stacks.Algebraization.epi_hom_of_epi` — an epimorphism of coherent modules is an epimorphism
  of sheaves of modules.

## References

* [Stacks Project, Tag 0899](https://stacks.math.columbia.edu/tag/0899)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Algebraization

variable {X : Scheme.{u}}

/-- A function on an affine open dies in `𝒪_X / J` exactly when it lies in `J`. -/
public theorem idealQuotientπ_app_eq_zero_iff (J : X.IdealSheafData) (U : X.affineOpens)
    (s : Γ(X, U.1)) :
    (cokernel.π (C := X.Modules)
        (idealPowerMultiple J 1 (SheafOfModules.unit X.ringCatSheaf)).ι).app U.1 s = 0 ↔
      s ∈ J.ideal U := by
  have h := idealPowerMultiple_unit_obj_affineOpens J 1 U
  rw [pow_one] at h
  exact (cokernel_π_app_eq_zero_iff (SheafOfModules.unit X.ringCatSheaf)
    (idealPowerMultiple J 1 (SheafOfModules.unit X.ringCatSheaf)) U.1 s).trans
    (Iff.of_eq (congrArg (s ∈ ·) h))

/-! ### Cyclic modules -/

/-- For a surjective linear map `g : R ⟶ M` from a commutative ring, the annihilator of `M` is the
kernel of `g`. -/
public theorem mem_annihilator_iff_of_surjective {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (g : R →ₗ[R] M) (hg : Function.Surjective g) (a : R) :
    a ∈ Module.annihilator R M ↔ g a = 0 := by
  rw [Module.mem_annihilator]
  refine ⟨fun h => ?_, fun h m => ?_⟩
  · have h1 := h (g 1)
    rwa [← map_smul, smul_eq_mul, mul_one] at h1
  obtain ⟨b, rfl⟩ := hg m
  rw [← map_smul, smul_eq_mul, mul_comm, ← smul_eq_mul, map_smul, h, smul_zero]

/-- For a surjective linear map `g : R ⟶ M` from a commutative ring and an ideal `L`, the
preimage of `L • M` is `Ann(M) + L`. -/
public theorem apply_mem_smul_top_iff_of_surjective {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (g : R →ₗ[R] M) (hg : Function.Surjective g) (L : Ideal R) (a : R) :
    g a ∈ L • (⊤ : Submodule R M) ↔ a ∈ Module.annihilator R M ⊔ L := by
  rw [← LinearMap.range_eq_top.2 hg, LinearMap.range_eq_map, ← Submodule.map_smul'',
    Submodule.mem_map]
  constructor
  · rintro ⟨b, hb, hab⟩
    have hb' : b ∈ L := by simpa using hb
    have : a - b ∈ Module.annihilator R M := by
      rw [mem_annihilator_iff_of_surjective g hg, map_sub, hab, sub_self]
    simpa using Submodule.add_mem_sup this hb'
  · intro ha
    obtain ⟨c, hc, b, hb, rfl⟩ := Submodule.mem_sup.1 ha
    refine ⟨b, by simpa using hb, ?_⟩
    rw [map_add, (mem_annihilator_iff_of_surjective g hg c).1 hc, zero_add]

/-! ### Sections of morphisms -/

/-- Cancelling an `eqToHom` against its inverse inside a composite. -/
public theorem comp_eqToHom_comp_eqToHom_comp {C : Type*} [Category C] {A B B' D : C}
    (f : A ⟶ B) (h : B = B') (g : B ⟶ D) :
    (f ≫ eqToHom h) ≫ eqToHom h.symm ≫ g = f ≫ g := by
  subst h
  simp

/-- Moving an isomorphism across an equation of composites. -/
public theorem comp_eq_comp_hom_of_comp_inv_eq {C : Type*} [Category C] {P Q R T U : C}
    {a : P ⟶ Q} {b : Q ⟶ T} {e : U ≅ T} {c : P ⟶ R} {d : R ⟶ U}
    (h : a ≫ b ≫ e.inv = c ≫ d) : a ≫ b = c ≫ d ≫ e.hom := by
  rw [← Category.assoc c, ← h]
  simp

/-- An isomorphism of sheaves of modules kills a section only if the section is zero. -/
public theorem iso_hom_app_eq_zero_iff {M N : X.Modules} (e : M ≅ N) (U : X.Opens) (x : Γ(M, U)) :
    Scheme.Modules.Hom.app e.hom U x = 0 ↔ x = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, map_zero]⟩
  have h' := congrArg (fun φ : M ⟶ M => Scheme.Modules.Hom.app φ U x) e.hom_inv_id
  change Scheme.Modules.Hom.app e.inv U (Scheme.Modules.Hom.app e.hom U x) = x at h'
  rw [← h', h, map_zero]

/-- The map on sections over `U` of a morphism `𝒪_X ⟶ M`, as a `Γ(X, U)`-linear map. -/
public def unitHomSectionsLinearMap {M : X.Modules}
    (φ : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ M) (U : X.Opens) :
    Γ(X, U) →ₗ[Γ(X, U)] Γ(M, U) where
  toFun a := Scheme.Modules.Hom.app φ U a
  map_add' a b := map_add _ (show Γ(SheafOfModules.unit X.ringCatSheaf, U) from a) b
  map_smul' r a := Scheme.Modules.Hom.app_smul φ r
    (show Γ(SheafOfModules.unit X.ringCatSheaf, U) from a)

/-! ### The ideal sheaf of a quotient of the structure sheaf -/

/-- **A quotient of `𝒪_X` cuts out its scheme-theoretic support.** Let `φ : 𝒪_X ⟶ 𝒢` be an
epimorphism onto a quasi-coherent module of finite type, and suppose that the projection
`𝒪_X ⟶ 𝒪_X / J` is `φ` followed by the projection `𝒢 ⟶ 𝒢 / 𝓘 ^ m 𝒢` and an isomorphism
`𝒢 / 𝓘 ^ m 𝒢 ≅ 𝒪_X / J`. Then `J` is the scheme-theoretic support of `𝒢` plus `𝓘 ^ m`.

On an affine open `U` the module `Γ(𝒢, U)` is the cyclic module `Γ(X, U) / Ann Γ(𝒢, U)`, and the
hypothesis says that a function lies in `J(U)` exactly when its image in `Γ(𝒢, U)` lies in
`𝓘(U) ^ m Γ(𝒢, U)`. -/
public theorem eq_schemeTheoreticSupport_sup_of_epi (𝓘 J : X.IdealSheafData) (m : ℕ)
    {G : X.Modules} [G.IsQuasicoherent] [G.IsFiniteType]
    (φ : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ G) (hφ : Epi φ)
    (e : idealPowerQuotient 𝓘 m G ≅
      idealPowerQuotient J 1 (SheafOfModules.unit X.ringCatSheaf))
    (h : cokernel.π (C := X.Modules)
        (idealPowerMultiple J 1 (SheafOfModules.unit X.ringCatSheaf)).ι =
      φ ≫ cokernel.π (C := X.Modules) (idealPowerMultiple 𝓘 m G).ι ≫ e.hom) :
    J = Scheme.Modules.schemeTheoreticSupport G ⊔ 𝓘 ^ m := by
  refine Scheme.IdealSheafData.ext (funext fun U => ?_)
  change J.ideal U = Module.annihilator Γ(X, U.1) Γ(G, U.1) ⊔ 𝓘.ideal U ^ m
  ext s
  let g := unitHomSectionsLinearMap φ U.1
  have hg : Function.Surjective g :=
    @Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen X _ _ φ _ _ hφ U.1 U.2
  rw [← idealQuotientπ_app_eq_zero_iff, ← apply_mem_smul_top_iff_of_surjective g hg,
    ← cokernel_π_idealPowerMultiple_app_eq_zero_iff, h]
  exact iso_hom_app_eq_zero_iff e U.1 _

/-- A coherent module is quasi-coherent and of finite type. -/
private theorem isQuasicoherent_isFiniteType_of_isCoherent_object [IsLocallyNoetherian X]
    (M : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) :
    (M.obj : X.Modules).IsQuasicoherent ∧ (M.obj : X.Modules).IsFiniteType :=
  haveI : M.obj.IsCoherent := M.property
  Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent M.obj

/-- A morphism of coherent modules which is an epimorphism among coherent modules is an
epimorphism of sheaves of modules: its cokernel is again coherent. -/
public theorem epi_hom_of_epi [IsLocallyNoetherian X]
    {M N : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf} (φ : M ⟶ N)
    [Epi φ] : Epi (C := X.Modules) φ.hom := by
  have hqcM := (isQuasicoherent_isFiniteType_of_isCoherent_object M).1
  have hqcN := (isQuasicoherent_isFiniteType_of_isCoherent_object N).1
  have hcohN : N.obj.IsCoherent := N.property
  have hqcQ : (cokernel (C := X.Modules) φ.hom).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel (M := M.obj)
      (N := N.obj) φ.hom
  have hepiπ : Epi (C := X.Modules) (cokernel.π (C := X.Modules) φ.hom) := coequalizer.π_epi
  have hcohQ : (cokernel (C := X.Modules) φ.hom).IsCoherent :=
    @Stacks.AlgebraicGeometry.CoherentSubquotients.isCoherent_of_epi X _ N.obj _ hcohN hqcQ
      (cokernel.π (C := X.Modules) φ.hom) hepiπ
  let Q : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf :=
    ⟨cokernel (C := X.Modules) φ.hom, hcohQ⟩
  let c : N ⟶ Q := ObjectProperty.homMk (cokernel.π (C := X.Modules) φ.hom)
  let z0 : (show X.Modules from N.obj) ⟶ cokernel (C := X.Modules) φ.hom := 0
  let z : N ⟶ Q := ObjectProperty.homMk z0
  have h0 : φ.hom ≫ cokernel.π (C := X.Modules) φ.hom = φ.hom ≫ z0 :=
    (cokernel.condition (C := X.Modules) φ.hom).trans
      (comp_zero (C := X.Modules) (f := φ.hom)).symm
  have hcz : φ ≫ c = φ ≫ z := ObjectProperty.hom_ext _ h0
  have hc : cokernel.π (C := X.Modules) φ.hom = z0 :=
    congrArg (fun k => k.hom) ((cancel_epi φ).1 hcz)
  exact Abelian.epi_of_cokernel_π_eq_zero (C := X.Modules) φ.hom hc

/-! ### The algebraization -/

/-- **Algebraization of a formal closed subscheme.** Let `X` be a locally Noetherian scheme and
`𝓘` a quasi-coherent ideal sheaf for which the completion functor `Coh(𝒪_X) ⥤ Coh(X, 𝓘)` is an
equivalence. If `(Jₙ)` is a sequence of quasi-coherent ideal sheaves with
`Jₙ = 𝓘 ^ (n + 1) ⊔ J_{n+1}`, there is a quasi-coherent ideal sheaf `K` with
`Jₙ = K ⊔ 𝓘 ^ (n + 1)` for every `n`. -/
public theorem exists_idealSheaf_sup_eq_of_isEquivalence [IsLocallyNoetherian X]
    (𝓘 : X.IdealSheafData) [(completionFunctor X 𝓘).IsEquivalence]
    (J : ℕ → X.IdealSheafData) (hJ : ∀ n, J n = 𝓘 ^ (n + 1) ⊔ J (n + 1)) :
    ∃ K : X.IdealSheafData, ∀ n, J n = K ⊔ 𝓘 ^ (n + 1) := by
  have hanti : Antitone J := antitone_nat_of_succ_le fun n => le_sup_right.trans (hJ n).ge
  have hle (n : ℕ) : 𝓘 ^ (n + 1) ≤ J n := le_sup_left.trans (hJ n).ge
  have hcohO : (SheafOfModules.unit X.ringCatSheaf : X.Modules).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_unit X
  let O : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf :=
    ⟨SheafOfModules.unit X.ringCatSheaf, hcohO⟩
  let C := completionFunctor X 𝓘
  let Fsys : Stacks.Coherent.CoherentAdicSystems 𝓘 :=
    ⟨idealQuotientSystem J hanti, isCoherentAdicSystem_idealQuotientSystem 𝓘 J hanti hle hJ⟩
  -- the system map from the completion of `𝒪_X`
  let ψapp (n : ℕ) : (C.obj O).obj.obj (op n) ⟶ (idealQuotientSystem J hanti).obj (op n) :=
    eqToHom (completionFunctor_obj X 𝓘 O n) ≫
      idealPowerQuotientMap 𝓘 (J n) (n + 1) 1 ((hle n).trans (pow_one (J n)).ge) (𝟙 _)
  have hψ (n : ℕ) : completionProjection X 𝓘 O n ≫ ψapp n =
      cokernel.π (C := X.Modules)
        (idealPowerMultiple (J n) 1 (SheafOfModules.unit X.ringCatSheaf)).ι :=
    (comp_eqToHom_comp_eqToHom_comp _ _ _).trans
      ((idealPowerQuotientMap_π _ _ _ _ _ _).trans (Category.id_comp _))
  let ψ : C.obj O ⟶ Fsys := ObjectProperty.homMk
    { app := fun n => ψapp n.unop
      naturality := fun m n g => (epi_completionProjection X 𝓘 O m.unop).left_cancellation _ _ <|
        ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ ψapp n.unop)
          (completionProjection_map X 𝓘 O g)).trans ((hψ n.unop).trans
            ((idealQuotientSystem_map_π J hanti g).symm.trans
              (congrArg (· ≫ Fsys.obj.map g) (hψ m.unop).symm))))).trans
          (Category.assoc _ _ _) }
  -- the module `𝒢` and the map `φ : 𝒪_X ⟶ 𝒢`
  let G := C.objPreimage Fsys
  let eG : C.obj G ≅ Fsys := C.objObjPreimageIso Fsys
  let φ : O ⟶ G := C.preimage (ψ ≫ eG.inv)
  have hφ : C.map φ = ψ ≫ eG.inv := C.map_preimage _
  let e (n : ℕ) : (C.obj G).obj.obj (op n) ≅ (idealQuotientSystem J hanti).obj (op n) :=
    ((ObjectProperty.ι _ ⋙ (evaluation _ _).obj (op n)).mapIso eG)
  have hrel (n : ℕ) : cokernel.π (C := X.Modules)
      (idealPowerMultiple (J n) 1 (SheafOfModules.unit X.ringCatSheaf)).ι =
      φ.hom ≫ completionProjection X 𝓘 G n ≫ (e n).hom := by
    have h1 := completionFunctor_map_quotient X 𝓘 φ n
    have h2 : (ψ ≫ eG.inv).hom.app (op n) = ψapp n ≫ (e n).inv := rfl
    rw [hφ, h2] at h1
    exact (hψ n).symm.trans (comp_eq_comp_hom_of_comp_inv_eq h1)
  -- `φ` is an epimorphism
  have hψapp (n : ℕ) : Epi (ψapp n) :=
    have : Epi (completionProjection X 𝓘 O n ≫ ψapp n) := (hψ n).symm ▸ epi_idealQuotientπ (J n)
    epi_of_epi (completionProjection X 𝓘 O n) _
  have hψepi : Epi ψ := ⟨fun {Z} u v huv => ObjectProperty.hom_ext _ (NatTrans.ext (funext
    fun n => (cancel_epi (ψapp n.unop)).1 (congrArg (fun k => k.hom.app n) huv)))⟩
  have hφepi : Epi φ := C.epi_of_epi_map (hφ ▸ epi_comp ψ eG.inv)
  obtain ⟨hqcG, hftG⟩ := isQuasicoherent_isFiniteType_of_isCoherent_object G
  exact ⟨Scheme.Modules.schemeTheoreticSupport (G.obj : X.Modules), fun n =>
    eq_schemeTheoreticSupport_sup_of_epi 𝓘 (J n) (n + 1) φ.hom (epi_hom_of_epi φ)
      (eqToIso (completionFunctor_obj X 𝓘 G n).symm ≪≫ e n) (hrel n)⟩

end Stacks.Algebraization

end
