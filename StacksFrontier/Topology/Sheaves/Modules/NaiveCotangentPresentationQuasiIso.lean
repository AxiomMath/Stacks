module

public import StacksFrontier.Algebra.Homology.DoubleQuasiIso
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangent
public import StacksFrontier.RingTheory.NaiveCotangent.ExtensionQuasiIso
public import StacksFrontier.Topology.Sheaves.Modules.ConormalSequenceStalkExtension
public import StacksFrontier.Topology.Sheaves.Modules.FreeAlgebraSheafStalk
public import StacksFrontier.Topology.Sheaves.Modules.StalkAcyclic

/-!
# The stalks of a polynomial presentation and of its comparison map

Let `a : A ⟶ B` be a morphism of sheaves of commutative rings on a topological space `X`, let
`α : E ⟶ B` be a family of generators and let `x` be a point of `X`.  Under the identification
`(A[E])ₓ ≅ Aₓ[Eₓ]` the stalk of the presentation `A[E] ⟶ B` is the evaluation
`MvPolynomial.aeval` at the germs of the generators, and under the identifications of the stalks
of the conormal sheaf and of the tensor-differentials sheaf the stalks of the two maps induced by
a factorisation of one presentation of `B` through another are the maps
`Algebra.Extension.Cotangent.map` and `Algebra.Extension.CotangentSpace.map` of the induced
morphism of stalk extensions.

## Main definitions

* `Stacks.SheafOfModules.presentationStalkVariable`: the map `Eₓ → Bₓ` sending the germ of a
  section `t` of `E` to the germ of `α(t)`.
* `Stacks.SheafOfModules.presentationStalkSection` and
  `Stacks.SheafOfModules.freeAlgebraStalkBackHom`: a set-theoretic section of the stalk of
  `A[E] ⟶ B` and the induced homomorphism `(A[B])ₓ → (A[E])ₓ`.
* `Stacks.SheafOfModules.stalkExtensionHomBack`: the morphism of stalk extensions from the
  canonical presentation to an arbitrary one.
* `Stacks.Sites.Conormal.conormalSheafMapOfFacStalk` and
  `Stacks.Sites.Conormal.tensorSheafMapOfFacStalk`: the maps induced on stalks by
  `Stacks.Sites.Conormal.conormalSheafMapOfFac` and
  `Stacks.Sites.Conormal.tensorSheafMapOfFac`.
* `AlgebraicGeometry.SheafOfModules.stalkObjAddEquivOfEq`: the identification of the stalks of
  two equal sheaves of modules.

## Main results

* `Stacks.SheafOfModules.stalkFunctor_map_presentation_apply`: the stalk of the presentation
  `A[E] ⟶ B` is evaluation of a polynomial over `Aₓ` at the germs of the generators.
* `Stacks.Sites.Conormal.conormalSheafMapOfFacStalk_eq_cotangentMap` and
  `Stacks.Sites.Conormal.tensorSheafMapOfFacStalk_eq_cotangentSpaceMap`: the stalks of the two
  maps of a change of presentation are the cotangent and cotangent-space maps of the induced
  morphism of stalk extensions.
* `Stacks.Sites.Conormal.tensorDifferentialsSheafStalk_hom_ext`: two additive maps out of the
  stalk of `B ⊗[A] Ω[A/R]` agreeing on the germs of the local sections `b ⊗ d f` are equal.
* `Stacks.Sites.Conormal.conormalSequenceStalkMapF_eq_cotangentComplex'`: the stalk of the
  left-hand map of the conormal sequence is the cotangent complex of the stalk extension, on
  every element of the stalk.
* `NaiveCotangent.IsQuasiIso.eq_zero_of_d_eq_zero`,
  `NaiveCotangent.IsQuasiIso.exists_of_d_eq_zero`, `NaiveCotangent.IsQuasiIso.exists_d_eq` and
  `NaiveCotangent.IsQuasiIso.exists_add_d_eq`: a quasi-isomorphism of two-term complexes,
  restated as four elementary statements about the kernel and the cokernel of the differential.
* `CochainComplex.quasiIso_of_isZero_X_of_addEquiv`: a morphism of complexes of modules
  concentrated in degrees `-1` and `0` is a quasi-isomorphism as soon as it is, after additive
  identifications of the four nonzero terms, bijective on the kernel and on the cokernel.
* `Stacks.SheafOfModules.quasiIso_naiveCotangentComplexComparison`: the canonical comparison
  map `NL(α) ⟶ NL_{B/A}` of a polynomial presentation `α : E ⟶ B` is a quasi-isomorphism.

## References

* [Stacks Project, Tag 08TL](https://stacks.math.columbia.edu/tag/08TL)
* [Stacks Project, Tag 08TU](https://stacks.math.columbia.edu/tag/08TU)
* [Stacks Project, Tag 00S1](https://stacks.math.columbia.edu/tag/00S1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TensorProduct

universe u

noncomputable section

/-! ### Stalks of a zero sheaf of modules and of an equality of sheaves of modules -/

namespace AlgebraicGeometry.SheafOfModules

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (x : X)

/-- Equal sheaves of modules have additively identified stalks. -/
def stalkObjAddEquivOfEq {M N : _root_.SheafOfModules.{u} O} (e : M = N) :
    ToType ((stalkFunctor O x).obj M) ≃+ ToType ((stalkFunctor O x).obj N) :=
  ((stalkFunctor O x).mapIso (eqToIso e)).toLinearEquiv.toAddEquiv

/-- The identification of the stalks of equal sheaves of modules is the stalk of the
corresponding `eqToHom`. -/
theorem stalkObjAddEquivOfEq_apply {M N : _root_.SheafOfModules.{u} O} (e : M = N)
    (z : ToType ((stalkFunctor O x).obj M)) :
    stalkObjAddEquivOfEq O x e z = (stalkFunctor O x).map (eqToHom e) z := rfl

/-- The inverse of the identification of the stalks of equal sheaves of modules is the stalk of
the `eqToHom` of the symmetric equality. -/
theorem stalkObjAddEquivOfEq_symm_apply {M N : _root_.SheafOfModules.{u} O} (e : M = N)
    (z : ToType ((stalkFunctor O x).obj N)) :
    (stalkObjAddEquivOfEq O x e).symm z = (stalkFunctor O x).map (eqToHom e.symm) z := by
  refine (stalkObjAddEquivOfEq O x e).injective ?_
  rw [AddEquiv.apply_symm_apply, stalkObjAddEquivOfEq_apply, ← ConcreteCategory.comp_apply,
    ← Functor.map_comp, eqToHom_trans, eqToHom_refl, CategoryTheory.Functor.map_id,
    ConcreteCategory.id_apply]

/-- The stalk functor preserves zero objects, being additive. -/
theorem isZero_stalkFunctor_obj (M : _root_.SheafOfModules.{u} O) (hM : IsZero M) :
    IsZero ((stalkFunctor O x).obj M) := by
  rw [IsZero.iff_id_eq_zero, ← CategoryTheory.Functor.map_id (stalkFunctor O x) M,
    (IsZero.iff_id_eq_zero M).mp hM, CategoryTheory.Functor.map_zero]

end AlgebraicGeometry.SheafOfModules

/-! ### Two elementary criteria -/

namespace NaiveCotangent

variable {S : Type*} [CommRing S] {T₁ T₂ : TwoTerm S} {f : ChainMap T₁ T₂}

/-- A quasi-isomorphism is injective on the kernel of the differential. -/
theorem IsQuasiIso.eq_zero_of_d_eq_zero (hf : IsQuasiIso f) (m : T₁.X₁) (h1 : T₁.d m = 0)
    (h2 : f.f₁ m = 0) : m = 0 :=
  congrArg Subtype.val (hf.1.1 (a₁ := ⟨m, h1⟩) (a₂ := 0)
    (Subtype.ext ((LinearMap.coe_restrict_apply _ _).trans
      (h2.trans (congrArg Subtype.val (map_zero f.onH₁)).symm))))

/-- A quasi-isomorphism is surjective on the kernel of the differential. -/
theorem IsQuasiIso.exists_of_d_eq_zero (hf : IsQuasiIso f) (m : T₂.X₁) (h1 : T₂.d m = 0) :
    ∃ n : T₁.X₁, T₁.d n = 0 ∧ f.f₁ n = m := by
  obtain ⟨n, hn⟩ := hf.1.2 ⟨m, h1⟩
  exact ⟨n.1, n.2, (LinearMap.coe_restrict_apply _ _).symm.trans (congrArg Subtype.val hn)⟩

/-- A quasi-isomorphism is injective on the cokernel of the differential. -/
theorem IsQuasiIso.exists_d_eq (hf : IsQuasiIso f) (n : T₁.X₀)
    (h : ∃ m : T₂.X₁, T₂.d m = f.f₀ n) : ∃ z : T₁.X₁, T₁.d z = n := by
  have h0 : f.onH₀ (Submodule.Quotient.mk n) = 0 :=
    (Submodule.mapQ_apply _ _ _ n).trans ((Submodule.Quotient.mk_eq_zero _).mpr h)
  exact (Submodule.Quotient.mk_eq_zero _).mp (hf.2.1 (h0.trans (map_zero f.onH₀).symm))

/-- A quasi-isomorphism is surjective on the cokernel of the differential. -/
theorem IsQuasiIso.exists_add_d_eq (hf : IsQuasiIso f) (n : T₂.X₀) :
    ∃ (m : T₁.X₀) (z : T₂.X₁), f.f₀ m + T₂.d z = n := by
  obtain ⟨t, ht⟩ := hf.2.2 (Submodule.Quotient.mk n)
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ t
  obtain ⟨z, hz⟩ := (Submodule.Quotient.eq _).mp ((Submodule.mapQ_apply _ _ _ m).symm.trans ht)
  exact ⟨m, -z, by rw [map_neg, hz]; abel⟩

end NaiveCotangent

namespace CochainComplex

variable {R : Type u} [Ring R] {K L : CochainComplex (ModuleCat.{u} R) ℤ}

/-- **Quasi-isomorphy of a two-term complex of modules, read through additive
identifications.**  A morphism of cochain complexes of modules which vanish outside degrees `-1`
and `0` is a quasi-isomorphism as soon as its differentials and its two nonzero components are,
after additive identifications of all four terms, bijective on the kernel and on the cokernel. -/
theorem quasiIso_of_isZero_X_of_addEquiv (φ : K ⟶ L)
    (hK : ∀ i : ℤ, i ≠ -1 → i ≠ 0 → IsZero (K.X i))
    (hL : ∀ i : ℤ, i ≠ -1 → i ≠ 0 → IsZero (L.X i))
    {M₁ N₁ M₂ N₂ : Type*} [AddCommGroup M₁] [AddCommGroup N₁] [AddCommGroup M₂]
    [AddCommGroup N₂]
    (u₁ : ToType (K.X (-1)) ≃+ M₁) (u₀ : ToType (K.X 0) ≃+ N₁)
    (v₁ : ToType (L.X (-1)) ≃+ M₂) (v₀ : ToType (L.X 0) ≃+ N₂)
    (d₁ : M₁ → N₁) (d₂ : M₂ → N₂) (p : M₁ → M₂) (q : N₁ → N₂)
    (hdK : ∀ z, K.d (-1) 0 z = u₀.symm (d₁ (u₁ z)))
    (hdL : ∀ z, L.d (-1) 0 z = v₀.symm (d₂ (v₁ z)))
    (hp : ∀ z, φ.f (-1) z = v₁.symm (p (u₁ z)))
    (hq : ∀ z, φ.f 0 z = v₀.symm (q (u₀ z)))
    (hinjKer : ∀ m : M₁, d₁ m = 0 → p m = 0 → m = 0)
    (hsurjKer : ∀ m : M₂, d₂ m = 0 → ∃ n : M₁, d₁ n = 0 ∧ p n = m)
    (hinjCoker : ∀ n : N₁, (∃ m : M₂, d₂ m = q n) → ∃ z : M₁, d₁ z = n)
    (hsurjCoker : ∀ n : N₂, ∃ (m : N₁) (z : M₂), q m + d₂ z = n) :
    QuasiIso φ := by
  refine quasiIso_of_isZero_X_of_bijective φ hK hL ?_ ?_ ?_ ?_
  · intro z hz hpz
    refine u₁.injective ((hinjKer (u₁ z) ?_ ?_).trans (map_zero u₁).symm)
    · exact u₀.symm.injective (((hdK z).symm.trans hz).trans (map_zero u₀.symm).symm)
    · exact v₁.symm.injective (((hp z).symm.trans hpz).trans (map_zero v₁.symm).symm)
  · intro y hy
    obtain ⟨n, hn₁, hn₂⟩ := hsurjKer (v₁ y)
      (v₀.symm.injective (((hdL y).symm.trans hy).trans (map_zero v₀.symm).symm))
    refine ⟨u₁.symm n, ?_, ?_⟩
    · refine (hdK (u₁.symm n)).trans ?_
      rw [u₁.apply_symm_apply, hn₁, map_zero]
    · refine (hp (u₁.symm n)).trans ?_
      rw [u₁.apply_symm_apply, hn₂, v₁.symm_apply_apply]
  · rintro z ⟨y, hy⟩
    obtain ⟨ζ, hζ⟩ := hinjCoker (u₀ z)
      ⟨v₁ y, v₀.symm.injective ((hdL y).symm.trans (hy.trans (hq z)))⟩
    refine ⟨u₁.symm ζ, ?_⟩
    refine (hdK (u₁.symm ζ)).trans ?_
    rw [u₁.apply_symm_apply, hζ, u₀.symm_apply_apply]
  · intro y
    obtain ⟨m, ζ, hmz⟩ := hsurjCoker (v₀ y)
    refine ⟨u₀.symm m, v₁.symm ζ, ?_⟩
    refine (congrArg₂ (· + ·) (hq (u₀.symm m)) (hdL (v₁.symm ζ))).trans ?_
    rw [u₀.apply_symm_apply, v₁.apply_symm_apply, ← map_add, hmz, v₀.symm_apply_apply]

end CochainComplex

/-! ### The stalk of a polynomial presentation -/

namespace Stacks.SheafOfModules

open TopCat.Presheaf Stacks.Sites.FreeAlgebra

variable {X : TopCat.{u}} (A B : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
  (a : A ⟶ B) (E : X.Presheaf (Type u))
  (α : E ⟶ Stacks.Sites.FreeAlgebra.underlyingPresheaf (Opens.grothendieckTopology X) B) (x : X)

/-- Restricting a section of `E` to a smaller neighbourhood of `x` does not change the germ of
its image under `α`. -/
theorem germ_app_res {U V : Opens X} (i : V ⟶ U) (hV : x ∈ V) (t : E.obj (op U)) :
    (germ B.obj V x hV).hom (α.app (op V) (E.map i.op t)) =
      (germ B.obj U x (i.le hV)).hom (α.app (op U) t) := by
  rw [NatTrans.naturality_apply α i.op t]
  exact germ_res_apply B.obj i x hV _

/-- The germs at `x` of the images of the generators, as a cocone over the diagram of sections
of `E` near `x`. -/
def presentationVariableCocone : Cocone ((OpenNhds.inclusion x).op ⋙ E) where
  pt := ToType (stalk B.obj x)
  ι :=
    { app := fun V ↦ TypeCat.ofHom fun t ↦
        (germ B.obj V.unop.1 x V.unop.2).hom (α.app (op V.unop.1) t)
      naturality := by
        intro V W f
        ext t
        exact germ_app_res B E α x ((OpenNhds.inclusion x).map f.unop) W.unop.2 t }

/-- The map `Eₓ → Bₓ` induced by a family of generators `α : E ⟶ B`: it sends the germ of a
section `t` of `E` to the germ of `α(t)`. -/
def presentationStalkVariable : E.stalk x → ToType (stalk B.obj x) :=
  (colimit.desc _ (presentationVariableCocone B E α x)).hom

/-- The germ of a section `t` of `E` goes to the germ of `α(t)`. -/
theorem presentationStalkVariable_germ (U : Opens X) (hx : x ∈ U) (t : E.obj (op U)) :
    presentationStalkVariable B E α x ((E.germ U x hx).hom t) =
      (germ B.obj U x hx).hom (α.app (op U) t) :=
  ConcreteCategory.congr_hom
    (colimit.ι_desc (presentationVariableCocone B E α x) (op (⟨U, hx⟩ : OpenNhds x))) t

/-- **The stalk of a polynomial presentation is an evaluation of polynomials.** Composed with
the identification `(A[E])ₓ ≅ Aₓ[Eₓ]`, the stalk of `A[E] ⟶ B` is the evaluation of a polynomial
over `Aₓ` at the germs of the generators, with coefficients read through the stalk of
`a : A ⟶ B`. -/
theorem stalkFunctor_map_presentation_comp_symm :
    (((stalkFunctor CommRingCat.{u} x).map
        (presentation (Opens.grothendieckTopology X) A B a E α).hom).hom).comp
        (freeAlgebraSheafStalkRingEquiv A E x).symm.toRingHom =
      MvPolynomial.eval₂Hom (((stalkFunctor CommRingCat.{u} x).map a.hom).hom)
        (presentationStalkVariable B E α x) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    have h : (freeAlgebraSheafStalkRingEquiv A E x).symm (MvPolynomial.C r) =
        ((stalkFunctor CommRingCat.{u} x).map
          (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A E).hom).hom r :=
      (RingEquiv.symm_apply_eq _).mpr
        (freeAlgebraSheafStalkRingEquiv_coefficientMap A E x r).symm
    refine Eq.trans ?_ (MvPolynomial.eval₂Hom_C _ _ r).symm
    refine Eq.trans (congrArg (((stalkFunctor CommRingCat.{u} x).map
      (presentation (Opens.grothendieckTopology X) A B a E α).hom).hom) h) ?_
    exact Stacks.Sites.Conormal.stalkFunctor_map_comp_apply
      (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A E)
      (presentation (Opens.grothendieckTopology X) A B a E α) a
      (freeAlgebraSheafCoefficientMap_comp_desc (Opens.grothendieckTopology X) A B E a α) x r
  · intro e
    obtain ⟨U, hx, t, rfl⟩ := exists_germ_eq E e
    have h : (freeAlgebraSheafStalkRingEquiv A E x).symm
          (MvPolynomial.X ((E.germ U x hx).hom t)) =
        (germ (freeAlgebraSheaf (Opens.grothendieckTopology X) A E).obj U x hx).hom
          ((freeAlgebraSheafVariable (Opens.grothendieckTopology X) A E).app (op U) t) :=
      (RingEquiv.symm_apply_eq _).mpr
        (freeAlgebraSheafStalkRingEquiv_variable A E x U hx t).symm
    refine Eq.trans ?_ (MvPolynomial.eval₂Hom_X' _ _ _).symm
    refine Eq.trans (congrArg (((stalkFunctor CommRingCat.{u} x).map
      (presentation (Opens.grothendieckTopology X) A B a E α).hom).hom) h) ?_
    refine Eq.trans (stalkFunctor_map_germ_apply U x hx
      (presentation (Opens.grothendieckTopology X) A B a E α).hom _) ?_
    refine Eq.trans ?_ (presentationStalkVariable_germ B E α x U hx t).symm
    exact congrArg (germ B.obj U x hx).hom
      (congrArg (fun s : E ⟶ underlyingPresheaf (Opens.grothendieckTopology X) B ↦ s.app (op U) t)
        (freeAlgebraSheafVariable_comp_desc (Opens.grothendieckTopology X) A B E a α))

/-- **The stalk of a polynomial presentation is an evaluation of polynomials**, stated on
elements of `(A[E])ₓ`. -/
theorem stalkFunctor_map_presentation_apply
    (p : ToType (stalk (freeAlgebraSheaf (Opens.grothendieckTopology X) A E).obj x)) :
    ((stalkFunctor CommRingCat.{u} x).map
        (presentation (Opens.grothendieckTopology X) A B a E α).hom).hom p =
      MvPolynomial.eval₂Hom (((stalkFunctor CommRingCat.{u} x).map a.hom).hom)
        (presentationStalkVariable B E α x) (freeAlgebraSheafStalkRingEquiv A E x p) := by
  refine Eq.trans (congrArg (((stalkFunctor CommRingCat.{u} x).map
    (presentation (Opens.grothendieckTopology X) A B a E α).hom).hom)
    ((freeAlgebraSheafStalkRingEquiv A E x).symm_apply_apply p).symm) ?_
  exact DFunLike.congr_fun (stalkFunctor_map_presentation_comp_symm A B a E α x)
    (freeAlgebraSheafStalkRingEquiv A E x p)

end Stacks.SheafOfModules

/-! ### The stalks of the maps of a change of presentation -/

namespace Stacks.Sites.Conormal

open Stacks.RelativeDifferentialStalk (algebraStalk)

section Generators

variable {X : TopCat.{u}} (R A B : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
  (a : R ⟶ A) (φ : A ⟶ B)
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) φ.hom] (x : X)

/-- Every element of the stalk of the conormal sheaf is the germ of the conormal class of a
section of the kernel. -/
theorem exists_germ_conormalClass_eq
    (ξ : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      (conormalSheaf (Opens.grothendieckTopology X) A B φ).val.presheaf x)) :
    ∃ (U : Opens X) (hx : x ∈ U) (y : kernelIdeal φ.hom (op U)),
      TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        (conormalSheaf (Opens.grothendieckTopology X) A B φ).val.presheaf U x hx
        (conormalClass (Opens.grothendieckTopology X) R A B a φ (op U) y) = ξ := by
  obtain ⟨z, hz⟩ := (stalkKernelIdeal φ.hom x).toCotangent_surjective
    (conormalSheafStalkLinearEquiv A B φ x ξ)
  obtain ⟨U, hx, y₀, hy₀, hgy⟩ := exists_germ_eq_of_mem_stalkKernelIdeal φ.hom x
    (z : ToType (TopCat.Presheaf.stalk A.obj x)) z.2
  refine ⟨U, hx, ⟨y₀, hy₀⟩, (conormalSheafStalkLinearEquiv A B φ x).injective ?_⟩
  refine Eq.trans (conormalSheafStalkLinearEquiv_germ_conormalClass A B φ x R a U hx
    ⟨y₀, hy₀⟩) ?_
  exact (congrArg (stalkKernelIdeal φ.hom x).toCotangent (Subtype.ext hgy)).trans hz

/-- The image of a zero section under the unit of sheafification vanishes. -/
theorem toAssociatedModule_zero
    (M : PresheafOfModules.{u} (quotientPresheaf φ.hom ⋙ forget₂ CommRingCat RingCat))
    (Y : (Opens X)ᵒᵖ) :
    toAssociatedModule (Opens.grothendieckTopology X) A B φ M Y 0 = 0 :=
  add_eq_left.mp
    (((toAssociatedModule_add (Opens.grothendieckTopology X) A B φ M Y 0 0).symm).trans
      (congrArg (toAssociatedModule (Opens.grothendieckTopology X) A B φ M Y)
        (add_zero (0 : M.obj Y))))

/-- Every element of the stalk of `B ⊗[A] Ω[A/R]` is the germ of a local section `1 ⊗ ω`. -/
theorem exists_germ_one_tmul_eq
    (ξ : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      (tensorDifferentialsSheaf (Opens.grothendieckTopology X) R A B a φ).val.presheaf x)) :
    ∃ (U : Opens X) (hx : x ∈ U) (ω : (differentialsPresheaf a.hom).obj (op U)),
      TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        (tensorDifferentialsSheaf (Opens.grothendieckTopology X) R A B a φ).val.presheaf U x hx
        (toAssociatedModule (Opens.grothendieckTopology X) A B φ
          (tensorPresheaf φ.hom a.hom) (op U)
          ((1 : A.obj.obj (op U) ⧸ kernelIdeal φ.hom (op U)) ⊗ₜ[A.obj.obj (op U)] ω)) = ξ := by
  obtain ⟨ζ, rfl⟩ := (tensorSheafStalkSheafifyLinearEquiv R A B a φ x).surjective ξ
  obtain ⟨U, hx, ω, rfl⟩ := exists_germ_eq_one_tmul φ.hom a.hom x ζ
  exact ⟨U, hx, ω, (tensorSheafStalkSheafifyLinearEquiv_germ R A B a φ x U hx _).symm⟩

/-- **Two additive maps out of the stalk of `B ⊗[A] Ω[A/R]` agreeing on the germs of the local
sections `b ⊗ d f` are equal.** -/
theorem tensorDifferentialsSheafStalk_hom_ext {M : Type u} [AddCommGroup M]
    (Φ Ψ : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      (tensorDifferentialsSheaf (Opens.grothendieckTopology X) R A B a φ).val.presheaf x) →+ M)
    (hgen : ∀ (U : Opens X) (hx : x ∈ U)
      (b : A.obj.obj (op U) ⧸ kernelIdeal φ.hom (op U)) (f : A.obj.obj (op U)),
      Φ (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          (tensorDifferentialsSheaf (Opens.grothendieckTopology X) R A B a φ).val.presheaf U x hx
          (toAssociatedModule (Opens.grothendieckTopology X) A B φ
            (tensorPresheaf φ.hom a.hom) (op U)
            (b ⊗ₜ[A.obj.obj (op U)]
              CommRingCat.KaehlerDifferential.d (f := a.hom.app (op U)) f))) =
        Ψ (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          (tensorDifferentialsSheaf (Opens.grothendieckTopology X) R A B a φ).val.presheaf U x hx
          (toAssociatedModule (Opens.grothendieckTopology X) A B φ
            (tensorPresheaf φ.hom a.hom) (op U)
            (b ⊗ₜ[A.obj.obj (op U)]
              CommRingCat.KaehlerDifferential.d (f := a.hom.app (op U)) f)))) :
    Φ = Ψ := by
  refine AddMonoidHom.ext fun ξ ↦ ?_
  obtain ⟨U, hx, ω₀, rfl⟩ := exists_germ_one_tmul_eq R A B a φ x ξ
  let := (a.hom.app (op U)).hom.toAlgebra
  let Θ : (A.obj.obj (op U) ⧸ kernelIdeal φ.hom (op U)) ⊗[A.obj.obj (op U)]
      KaehlerDifferential (R.obj.obj (op U)) (A.obj.obj (op U)) →+
      ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (tensorDifferentialsSheaf (Opens.grothendieckTopology X) R A B a φ).val.presheaf x) :=
    (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
      (tensorDifferentialsSheaf (Opens.grothendieckTopology X) R A B a φ).val.presheaf
      U x hx).hom.comp
      (AddMonoidHom.mk' (toAssociatedModule (Opens.grothendieckTopology X) A B φ
        (tensorPresheaf φ.hom a.hom) (op U))
        (toAssociatedModule_add _ A B φ (tensorPresheaf φ.hom a.hom) (op U)))
  have hω : ∀ (ω : KaehlerDifferential (R.obj.obj (op U)) (A.obj.obj (op U)))
      (b : A.obj.obj (op U) ⧸ kernelIdeal φ.hom (op U)),
      Φ (Θ (b ⊗ₜ[A.obj.obj (op U)] ω)) = Ψ (Θ (b ⊗ₜ[A.obj.obj (op U)] ω)) := by
    intro ω
    have mem : ω ∈ Submodule.span (A.obj.obj (op U))
        (Set.range (KaehlerDifferential.D (R.obj.obj (op U)) (A.obj.obj (op U)))) := by
      rw [KaehlerDifferential.span_range_derivation]; trivial
    induction mem using Submodule.span_induction with
    | mem y hy => obtain ⟨y, rfl⟩ := hy; exact fun b ↦ hgen U hx b y
    | zero => intro b; simp only [TensorProduct.tmul_zero, map_zero]
    | add ω₁ ω₂ _ _ ih₁ ih₂ =>
        intro b
        simp only [TensorProduct.tmul_add, map_add, ih₁ b, ih₂ b]
    | smul r ω _ ih => intro b; rw [← TensorProduct.smul_tmul]; exact ih _
  exact hω ω₀ 1

end Generators

/-! ### Germs of tensors of a scalar and a differential -/

section Presheaf

variable {X : TopCat.{u}} {A B : X.Presheaf CommRingCat.{u}} (φ : A ⟶ B)
  {R : X.Presheaf CommRingCat.{u}} (a : R ⟶ A) (x : X)

/-- The comparison map sends the germ of `b ⊗ ω` to the tensor of the germs. -/
theorem tensorStalkHom_germ_tmul (U : Opens X) (hx : x ∈ U)
    (b : A.obj (op U) ⧸ kernelIdeal φ (op U))
    (ω : (differentialsPresheaf a).obj (op U)) :
    tensorStalkHom φ a x (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        (tensorPresheafOverSource φ a).presheaf U x hx (b ⊗ₜ[A.obj (op U)] ω)) =
      germQuotientₛₗ φ x U hx b ⊗ₜ[ToType (A.stalk x)]
        TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          (differentialsPresheaf a).presheaf U x hx ω :=
  (tensorStalkHom_germ φ a x U hx _).trans
    (TensorProduct.map_tmul (germQuotientₛₗ φ x U hx) (germOmegaₛₗ a x U hx) b ω)

section Kaehler

variable [DecidableEq (OrderDual (TopologicalSpace.OpenNhds x))]

/-- The identification of the stalk of `U ↦ (A(U)/I(U)) ⊗[A(U)] Ω[A(U)/R(U)]` with
`(Aₓ/Iₓ) ⊗[Aₓ] Ω[Aₓ/Rₓ]` carries the germ of `b ⊗ d f` to the tensor of the germ of `b` with
`d (fₓ)`. -/
theorem tensorPresheafStalkKaehlerLinearEquiv_germ_tmul_d (U : Opens X) (hx : x ∈ U)
    (b : A.obj (op U) ⧸ kernelIdeal φ (op U)) (f : A.obj (op U)) :
    letI := algebraStalk a x
    tensorPresheafStalkKaehlerLinearEquiv φ a x
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          (tensorPresheafOverSource φ a).presheaf U x hx
          (b ⊗ₜ[A.obj (op U)] CommRingCat.KaehlerDifferential.d (f := a.app (op U)) f)) =
      germQuotientₛₗ φ x U hx b ⊗ₜ[ToType (A.stalk x)]
        KaehlerDifferential.D (ToType (R.stalk x)) (ToType (A.stalk x))
          ((A.germ U x hx).hom f) := by
  let := algebraStalk a x
  refine Eq.trans (congrArg (TensorProduct.congr (LinearEquiv.refl _ _)
      (Stacks.RelativeDifferentialStalk.stalkLinearEquiv a x))
      (tensorStalkHom_germ_tmul φ a x U hx b _)) ?_
  refine (TensorProduct.congr_tmul (LinearEquiv.refl _ _)
    (Stacks.RelativeDifferentialStalk.stalkLinearEquiv a x) _ _).trans ?_
  exact congrArg (fun ω : KaehlerDifferential (ToType (R.stalk x)) (ToType (A.stalk x)) ↦
      germQuotientₛₗ φ x U hx b ⊗ₜ[ToType (A.stalk x)] ω)
    (Stacks.RelativeDifferentialStalk.stalkLinearEquiv_germ_D a x
      (OrderDual.toDual (⟨U, hx⟩ : TopologicalSpace.OpenNhds x)) f)

end Kaehler

end Presheaf

section Sheaf

variable {X : TopCat.{u}} (R A B : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
  (a : R ⟶ A) (φ : A ⟶ B)
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) φ.hom] (x : X)
  [DecidableEq (OrderDual (TopologicalSpace.OpenNhds x))]

/-- The identification of the stalk of `B ⊗[A] Ω[A/R]` with the cotangent space of the stalk
extension carries the germ of the local section `b ⊗ d f` to the tensor of the image of the germ
of `b` in `Bₓ` with `d (fₓ)`. -/
theorem cotangentSpaceStalkLinearEquiv_germ_tmul_d (U : Opens X) (hx : x ∈ U)
    (b : A.obj.obj (op U) ⧸ kernelIdeal φ.hom (op U)) (f : A.obj.obj (op U)) :
    letI := algebraStalk a.hom x
    letI := algebraStalk φ.hom x
    cotangentSpaceStalkLinearEquiv R A B a φ x
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          (tensorDifferentialsSheaf (Opens.grothendieckTopology X) R A B a φ).val.presheaf U x hx
          (toAssociatedModule (Opens.grothendieckTopology X) A B φ
            (tensorPresheaf φ.hom a.hom) (op U)
            (b ⊗ₜ[A.obj.obj (op U)]
              CommRingCat.KaehlerDifferential.d (f := a.hom.app (op U)) f))) =
      stalkQuotientLinearEquiv φ.hom x (germQuotientₛₗ φ.hom x U hx b)
        ⊗ₜ[ToType (TopCat.Presheaf.stalk A.obj x)]
        KaehlerDifferential.D (ToType (TopCat.Presheaf.stalk R.obj x))
          (ToType (TopCat.Presheaf.stalk A.obj x))
          ((TopCat.Presheaf.germ A.obj U x hx).hom f) := by
  let := algebraStalk a.hom x
  let := algebraStalk φ.hom x
  have hE := tensorSheafStalkSheafifyLinearEquiv_germ R A B a φ x U hx
    (b ⊗ₜ[A.obj.obj (op U)] CommRingCat.KaehlerDifferential.d (f := a.hom.app (op U)) f)
  have step : tensorDifferentialsSheafStalkLinearEquiv R A B a φ x
      (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        (tensorDifferentialsSheaf (Opens.grothendieckTopology X) R A B a φ).val.presheaf U x hx
        (toAssociatedModule (Opens.grothendieckTopology X) A B φ
          (tensorPresheaf φ.hom a.hom) (op U)
          (b ⊗ₜ[A.obj.obj (op U)]
            CommRingCat.KaehlerDifferential.d (f := a.hom.app (op U)) f))) =
      germQuotientₛₗ φ.hom x U hx b ⊗ₜ[ToType (TopCat.Presheaf.stalk A.obj x)]
        KaehlerDifferential.D (ToType (TopCat.Presheaf.stalk R.obj x))
          (ToType (TopCat.Presheaf.stalk A.obj x))
          ((TopCat.Presheaf.germ A.obj U x hx).hom f) := by
    change tensorPresheafStalkKaehlerLinearEquiv φ.hom a.hom x
      ((tensorSheafStalkSheafifyLinearEquiv R A B a φ x).symm _) = _
    refine Eq.trans (congrArg (tensorPresheafStalkKaehlerLinearEquiv φ.hom a.hom x)
      ((LinearEquiv.symm_apply_eq _).mpr hE.symm)) ?_
    exact tensorPresheafStalkKaehlerLinearEquiv_germ_tmul_d φ.hom a.hom x U hx b f
  refine Eq.trans (congrArg (TensorProduct.congr (stalkQuotientLinearEquiv φ.hom x)
      (LinearEquiv.refl (ToType (TopCat.Presheaf.stalk A.obj x))
        (KaehlerDifferential (ToType (TopCat.Presheaf.stalk R.obj x))
          (ToType (TopCat.Presheaf.stalk A.obj x))))) step) ?_
  exact TensorProduct.congr_tmul (stalkQuotientLinearEquiv φ.hom x) _ _ _

/-- **The stalk of the left-hand map of the conormal sequence is the cotangent complex of the
stalk extension**, on every element of the stalk. -/
theorem conormalSequenceStalkMapF_eq_cotangentComplex' (c : R ⟶ B) (hc : a ≫ φ = c)
    (ξ : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      (conormalSheaf (Opens.grothendieckTopology X) A B φ).val.presheaf x)) :
    letI := algebraStalk a.hom x
    letI := algebraStalk φ.hom x
    letI := stalkAlgebraBase R B c x
    cotangentSpaceStalkLinearEquiv R A B a φ x (conormalSequenceStalkMapF R A B a φ x ξ) =
      (stalkExtension R A B a φ c x hc).cotangentComplex
        (conormalSheafStalkLinearEquiv A B φ x ξ) := by
  let := algebraStalk a.hom x
  let := algebraStalk φ.hom x
  let := stalkAlgebraBase R B c x
  obtain ⟨y, hy⟩ := (stalkKernelIdeal φ.hom x).toCotangent_surjective
    (conormalSheafStalkLinearEquiv A B φ x ξ)
  have hξ : ξ = (conormalSheafStalkLinearEquiv A B φ x).symm
      ((stalkKernelIdeal φ.hom x).toCotangent y) :=
    ((LinearEquiv.symm_apply_eq _).mpr hy).symm
  refine Eq.trans (congrArg (fun t ↦ cotangentSpaceStalkLinearEquiv R A B a φ x
    (conormalSequenceStalkMapF R A B a φ x t)) hξ) ?_
  refine Eq.trans (conormalSequenceStalkMapF_eq_cotangentComplex R A B a φ c x hc y) ?_
  exact congrArg (stalkExtension R A B a φ c x hc).cotangentComplex hy

end Sheaf

/-! ### The stalks of the maps induced by a factorisation -/

section Comparison

variable {X : TopCat.{u}} (R A₁ A₂ B : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
  (a₁ : R ⟶ A₁) (a₂ : R ⟶ A₂) (φ₁ : A₁ ⟶ B) (φ₂ : A₂ ⟶ B) (h : A₁ ⟶ A₂)
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) φ₁.hom]
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) φ₂.hom] (x : X)
  (hφ : h ≫ φ₂ = φ₁) (ha : a₁ ≫ h = a₂)

/-- The map induced on the stalks of the conormal sheaves by a factorisation
`h ≫ φ₂ = φ₁`. -/
def conormalSheafMapOfFacStalk :
    ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (conormalSheaf (Opens.grothendieckTopology X) A₁ B φ₁).val.presheaf x) →+
      ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (conormalSheaf (Opens.grothendieckTopology X) A₂ B φ₂).val.presheaf x) :=
  ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    ((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf B).obj).map
      (conormalSheafMapOfFac (Opens.grothendieckTopology X) B A₁ A₂ φ₁ φ₂ h hφ).val)).hom

/-- The stalk of the map of conormal sheaves carries the germ of a section to the germ of its
image. -/
theorem conormalSheafMapOfFacStalk_germ (U : Opens X) (hx : x ∈ U)
    (s : (conormalSheaf (Opens.grothendieckTopology X) A₁ B φ₁).val.obj (op U)) :
    conormalSheafMapOfFacStalk A₁ A₂ B φ₁ φ₂ h x hφ
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          (conormalSheaf (Opens.grothendieckTopology X) A₁ B φ₁).val.presheaf U x hx s) =
      TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        (conormalSheaf (Opens.grothendieckTopology X) A₂ B φ₂).val.presheaf U x hx
        ((conormalSheafMapOfFac (Opens.grothendieckTopology X) B A₁ A₂ φ₁ φ₂ h hφ).val.app
          (op U) s) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply' U x hx
    ((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf B).obj).map
      (conormalSheafMapOfFac (Opens.grothendieckTopology X) B A₁ A₂ φ₁ φ₂ h hφ).val) s

/-- **The stalk of the map of conormal sheaves is the cotangent map of the induced morphism of
stalk extensions.**  Both send the germ of the conormal class of a section `y` of the kernel of
`φ₁` to the conormal class of the germ of `h(y)`. -/
theorem conormalSheafMapOfFacStalk_eq_cotangentMap (c : R ⟶ B)
    (hc₁ : a₁ ≫ φ₁ = c) (hc₂ : a₂ ≫ φ₂ = c)
    (ξ : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      (conormalSheaf (Opens.grothendieckTopology X) A₁ B φ₁).val.presheaf x)) :
    letI := stalkAlgebraBase R B c x
    conormalSheafStalkLinearEquiv A₂ B φ₂ x
        (conormalSheafMapOfFacStalk A₁ A₂ B φ₁ φ₂ h x hφ ξ) =
      Algebra.Extension.Cotangent.map
          (stalkExtensionHom R A₁ A₂ B a₁ a₂ φ₁ φ₂ c h x hc₁ hc₂ ha hφ)
        (conormalSheafStalkLinearEquiv A₁ B φ₁ x ξ) := by
  let := stalkAlgebraBase R B c x
  obtain ⟨U, hx, y, rfl⟩ := exists_germ_conormalClass_eq R A₁ B a₁ φ₁ x ξ
  refine Eq.trans (congrArg (conormalSheafStalkLinearEquiv A₂ B φ₂ x)
    ((conormalSheafMapOfFacStalk_germ A₁ A₂ B φ₁ φ₂ h x hφ U hx _).trans
      (congrArg (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        (conormalSheaf (Opens.grothendieckTopology X) A₂ B φ₂).val.presheaf U x hx).hom
        (conormalSheafMapOfFac_conormalClass (Opens.grothendieckTopology X) R B A₁ A₂ a₁ a₂
          φ₁ φ₂ h hφ (op U) y)))) ?_
  refine Eq.trans (conormalSheafStalkLinearEquiv_germ_conormalClass A₂ B φ₂ x R a₂ U hx _) ?_
  refine Eq.symm (Eq.trans (congrArg (Algebra.Extension.Cotangent.map
    (stalkExtensionHom R A₁ A₂ B a₁ a₂ φ₁ φ₂ c h x hc₁ hc₂ ha hφ))
    (conormalSheafStalkLinearEquiv_germ_conormalClass A₁ B φ₁ x R a₁ U hx y)) ?_)
  refine Eq.trans (Algebra.Extension.Cotangent.map_mk
    (stalkExtensionHom R A₁ A₂ B a₁ a₂ φ₁ φ₂ c h x hc₁ hc₂ ha hφ) _) ?_
  exact congrArg (stalkKernelIdeal φ₂.hom x).toCotangent
    (Subtype.ext (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx h.hom
      (y : A₁.obj.obj (op U))))

/-- The map of tensor-differentials sheaves induced by a factorisation sends the image of
`b ⊗ d f` under the unit of sheafification to the image of `h(b) ⊗ d (h f)`. -/
theorem tensorSheafMapOfFac_toAssociatedModule_tmul_d (U : (Opens X)ᵒᵖ)
    (b : A₁.obj.obj U ⧸ kernelIdeal φ₁.hom U) (f : A₁.obj.obj U) :
    (tensorSheafMapOfFac (Opens.grothendieckTopology X) R B A₁ A₂ a₁ a₂ φ₁ φ₂ h hφ
          ha).val.app U
        (toAssociatedModule (Opens.grothendieckTopology X) A₁ B φ₁
          (tensorPresheaf φ₁.hom a₁.hom) U
          (b ⊗ₜ[A₁.obj.obj U] CommRingCat.KaehlerDifferential.d (f := a₁.hom.app U) f)) =
      toAssociatedModule (Opens.grothendieckTopology X) A₂ B φ₂
        (tensorPresheaf φ₂.hom a₂.hom) U
        (quotientMapOfFac φ₁.hom φ₂.hom h.hom (hom_of_comp_eq hφ) U b ⊗ₜ[A₂.obj.obj U]
          CommRingCat.KaehlerDifferential.d (f := a₂.hom.app U) (h.hom.app U f)) := by
  refine Eq.trans (sheafifyLiftDesc_toAssociatedModule (Opens.grothendieckTopology X) A₁ B φ₁
    (tensorPresheaf φ₁.hom a₁.hom) _ _ _ _ _ U _) ?_
  refine congrArg (toAssociatedModule (Opens.grothendieckTopology X) A₂ B φ₂
    (tensorPresheaf φ₂.hom a₂.hom) U) ?_
  refine (TensorProduct.map_tmul _ _ _ _).trans ?_
  exact congrArg₂ (fun q (ω : (differentialsPresheaf a₂.hom).obj U) ↦ q ⊗ₜ[A₂.obj.obj U] ω)
    rfl (differentialsMapOfFac_d h.hom a₁.hom a₂.hom (hom_of_comp_eq ha) U f)

/-- The map induced on the stalks of the tensor-differentials sheaves by a factorisation
`h ≫ φ₂ = φ₁` over `R`. -/
def tensorSheafMapOfFacStalk :
    ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (tensorDifferentialsSheaf (Opens.grothendieckTopology X) R A₁ B a₁ φ₁).val.presheaf x) →+
      ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (tensorDifferentialsSheaf (Opens.grothendieckTopology X) R A₂ B a₂ φ₂).val.presheaf x) :=
  ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    ((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf B).obj).map
      (tensorSheafMapOfFac (Opens.grothendieckTopology X) R B A₁ A₂ a₁ a₂ φ₁ φ₂ h hφ ha).val)).hom

/-- The stalk of the map of tensor-differentials sheaves carries the germ of a section to the
germ of its image. -/
theorem tensorSheafMapOfFacStalk_germ (U : Opens X) (hx : x ∈ U)
    (s : (tensorDifferentialsSheaf (Opens.grothendieckTopology X) R A₁ B a₁ φ₁).val.obj (op U)) :
    tensorSheafMapOfFacStalk R A₁ A₂ B a₁ a₂ φ₁ φ₂ h x hφ ha
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          (tensorDifferentialsSheaf (Opens.grothendieckTopology X) R A₁ B a₁ φ₁).val.presheaf
          U x hx s) =
      TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        (tensorDifferentialsSheaf (Opens.grothendieckTopology X) R A₂ B a₂ φ₂).val.presheaf
        U x hx
        ((tensorSheafMapOfFac (Opens.grothendieckTopology X) R B A₁ A₂ a₁ a₂ φ₁ φ₂ h hφ
          ha).val.app (op U) s) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply' U x hx
    ((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf B).obj).map
      (tensorSheafMapOfFac (Opens.grothendieckTopology X) R B A₁ A₂ a₁ a₂ φ₁ φ₂ h hφ ha).val) s

/-- **The stalk of the map of tensor-differentials sheaves is the cotangent-space map of the
induced morphism of stalk extensions.**  Both send the germ of the local section `b ⊗ d f` to the
tensor of the image of the germ of `b` with `d (h(f)ₓ)`. -/
theorem tensorSheafMapOfFacStalk_eq_cotangentSpaceMap (c : R ⟶ B)
    (hc₁ : a₁ ≫ φ₁ = c) (hc₂ : a₂ ≫ φ₂ = c)
    [DecidableEq (OrderDual (TopologicalSpace.OpenNhds x))]
    (ξ : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      (tensorDifferentialsSheaf (Opens.grothendieckTopology X) R A₁ B a₁ φ₁).val.presheaf x)) :
    letI := algebraStalk a₁.hom x
    letI := algebraStalk φ₁.hom x
    letI := algebraStalk a₂.hom x
    letI := algebraStalk φ₂.hom x
    letI := stalkAlgebraBase R B c x
    cotangentSpaceStalkLinearEquiv R A₂ B a₂ φ₂ x
        (tensorSheafMapOfFacStalk R A₁ A₂ B a₁ a₂ φ₁ φ₂ h x hφ ha ξ) =
      Algebra.Extension.CotangentSpace.map
          (stalkExtensionHom R A₁ A₂ B a₁ a₂ φ₁ φ₂ c h x hc₁ hc₂ ha hφ)
        (cotangentSpaceStalkLinearEquiv R A₁ B a₁ φ₁ x ξ) := by
  let := algebraStalk a₁.hom x
  let := algebraStalk φ₁.hom x
  let := algebraStalk a₂.hom x
  let := algebraStalk φ₂.hom x
  let := stalkAlgebraBase R B c x
  refine DFunLike.congr_fun (tensorDifferentialsSheafStalk_hom_ext R A₁ B a₁ φ₁ x
    ((cotangentSpaceStalkLinearEquiv R A₂ B a₂ φ₂ x).toLinearMap.toAddMonoidHom.comp
      (tensorSheafMapOfFacStalk R A₁ A₂ B a₁ a₂ φ₁ φ₂ h x hφ ha))
    ((Algebra.Extension.CotangentSpace.map
        (stalkExtensionHom R A₁ A₂ B a₁ a₂ φ₁ φ₂ c h x hc₁ hc₂ ha hφ)).toAddMonoidHom.comp
      (cotangentSpaceStalkLinearEquiv R A₁ B a₁ φ₁ x).toLinearMap.toAddMonoidHom) ?_) ξ
  intro U hx b f
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  change cotangentSpaceStalkLinearEquiv R A₂ B a₂ φ₂ x
      (tensorSheafMapOfFacStalk R A₁ A₂ B a₁ a₂ φ₁ φ₂ h x hφ ha _) = _
  refine Eq.trans (congrArg (cotangentSpaceStalkLinearEquiv R A₂ B a₂ φ₂ x)
    ((tensorSheafMapOfFacStalk_germ R A₁ A₂ B a₁ a₂ φ₁ φ₂ h x hφ ha U hx _).trans
      (congrArg (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        (tensorDifferentialsSheaf (Opens.grothendieckTopology X) R A₂ B a₂ φ₂).val.presheaf
        U x hx).hom
        (tensorSheafMapOfFac_toAssociatedModule_tmul_d R A₁ A₂ B a₁ a₂ φ₁ φ₂ h hφ ha
          (op U) _ f)))) ?_
  refine Eq.trans (cotangentSpaceStalkLinearEquiv_germ_tmul_d R A₂ B a₂ φ₂ x U hx _ _) ?_
  refine Eq.symm (Eq.trans (congrArg (Algebra.Extension.CotangentSpace.map
      (stalkExtensionHom R A₁ A₂ B a₁ a₂ φ₁ φ₂ c h x hc₁ hc₂ ha hφ))
    (cotangentSpaceStalkLinearEquiv_germ_tmul_d R A₁ B a₁ φ₁ x U hx _ f)) ?_)
  refine Eq.trans (Algebra.Extension.CotangentSpace.map_tmul
    (stalkExtensionHom R A₁ A₂ B a₁ a₂ φ₁ φ₂ c h x hc₁ hc₂ ha hφ) _ _) ?_
  refine congrArg₂ (fun (bb : ToType (TopCat.Presheaf.stalk B.obj x))
      (ω : KaehlerDifferential (ToType (TopCat.Presheaf.stalk R.obj x))
        (ToType (TopCat.Presheaf.stalk A₂.obj x))) ↦
      bb ⊗ₜ[ToType (TopCat.Presheaf.stalk A₂.obj x)] ω) ?_ ?_
  · refine Eq.trans (Algebra.algebraMap_self_apply _) (Eq.symm ?_)
    refine Eq.trans ?_ (stalkFunctor_map_comp_apply h φ₂ φ₁ hφ x
      ((TopCat.Presheaf.germ A₁.obj U x hx).hom b))
    exact congrArg ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map φ₂.hom).hom
      (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx h.hom b).symm
  · exact congrArg (KaehlerDifferential.D (ToType (TopCat.Presheaf.stalk R.obj x))
      (ToType (TopCat.Presheaf.stalk A₂.obj x)))
      (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx h.hom f)

end Comparison

end Stacks.Sites.Conormal

/-! ### A morphism of stalk extensions back from the canonical presentation -/

namespace Stacks.SheafOfModules

open TopCat.Presheaf Stacks.Sites.FreeAlgebra Stacks.Sites.Conormal

variable {X : TopCat.{u}} (A B : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
  (a : A ⟶ B) (E : X.Presheaf (Type u))
  (α : E ⟶ Stacks.Sites.FreeAlgebra.underlyingPresheaf (Opens.grothendieckTopology X) B)
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
    (presentation (Opens.grothendieckTopology X) A B a E α).hom] (x : X)

/-- A set-theoretic section of the stalk of the presentation `A[E] ⟶ B`, on the stalk of the
underlying presheaf of sets of `B`. -/
def presentationStalkSection :
    stalk (C := Type u) (underlyingPresheaf (Opens.grothendieckTopology X) B) x →
      ToType (stalk (freeAlgebraSheaf (Opens.grothendieckTopology X) A E).obj x) :=
  fun t ↦ Function.surjInv
    (stalkMap_surjective (presentation (Opens.grothendieckTopology X) A B a E α).hom x)
    (presentationStalkVariable B (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _) x t)

/-- The section is a section of the stalk of the presentation. -/
theorem presentationStalkSection_spec
    (t : stalk (C := Type u) (underlyingPresheaf (Opens.grothendieckTopology X) B) x) :
    ((stalkFunctor CommRingCat.{u} x).map
        (presentation (Opens.grothendieckTopology X) A B a E α).hom).hom
        (presentationStalkSection A B a E α x t) =
      presentationStalkVariable B (underlyingPresheaf (Opens.grothendieckTopology X) B)
        (𝟙 _) x t :=
  Function.surjInv_eq
    (stalkMap_surjective (presentation (Opens.grothendieckTopology X) A B a E α).hom x) _

/-- The homomorphism `(A[B])ₓ → (A[E])ₓ` over `Aₓ` and over `Bₓ` obtained by evaluating a
polynomial over `Aₓ` at a set-theoretic section of the stalk of the presentation `A[E] ⟶ B`. -/
def freeAlgebraStalkBackHom :
    ToType (stalk (freeAlgebraSheaf (Opens.grothendieckTopology X) A
        (underlyingPresheaf (Opens.grothendieckTopology X) B)).obj x) →+*
      ToType (stalk (freeAlgebraSheaf (Opens.grothendieckTopology X) A E).obj x) :=
  (MvPolynomial.eval₂Hom
      (((stalkFunctor CommRingCat.{u} x).map
        (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A E).hom).hom)
      (presentationStalkSection A B a E α x)).comp
    (freeAlgebraSheafStalkRingEquiv A
      (underlyingPresheaf (Opens.grothendieckTopology X) B) x).toRingHom

/-- Evaluating at a section of the presentation and then applying the presentation again is
evaluating at the generators of the canonical presentation. -/
theorem stalkMap_presentation_comp_section :
    (((stalkFunctor CommRingCat.{u} x).map
        (presentation (Opens.grothendieckTopology X) A B a E α).hom).hom).comp
        (MvPolynomial.eval₂Hom
          (((stalkFunctor CommRingCat.{u} x).map
            (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A E).hom).hom)
          (presentationStalkSection A B a E α x)) =
      MvPolynomial.eval₂Hom (((stalkFunctor CommRingCat.{u} x).map a.hom).hom)
        (presentationStalkVariable B (underlyingPresheaf (Opens.grothendieckTopology X) B)
          (𝟙 _) x) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    refine Eq.trans ?_ (MvPolynomial.eval₂Hom_C _ _ r).symm
    refine Eq.trans (congrArg (((stalkFunctor CommRingCat.{u} x).map
      (presentation (Opens.grothendieckTopology X) A B a E α).hom).hom)
      (MvPolynomial.eval₂Hom_C _ _ r)) ?_
    exact Stacks.Sites.Conormal.stalkFunctor_map_comp_apply
      (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A E)
      (presentation (Opens.grothendieckTopology X) A B a E α) a
      (freeAlgebraSheafCoefficientMap_comp_desc (Opens.grothendieckTopology X) A B E a α) x r
  · intro t
    refine Eq.trans ?_ (MvPolynomial.eval₂Hom_X' _ _ t).symm
    refine Eq.trans (congrArg (((stalkFunctor CommRingCat.{u} x).map
      (presentation (Opens.grothendieckTopology X) A B a E α).hom).hom)
      (MvPolynomial.eval₂Hom_X' _ _ t)) ?_
    exact presentationStalkSection_spec A B a E α x t

/-- The homomorphism `(A[B])ₓ → (A[E])ₓ` is compatible with the two presentations of `Bₓ`. -/
theorem stalkMap_presentation_freeAlgebraStalkBackHom
    (y : ToType (stalk (freeAlgebraSheaf (Opens.grothendieckTopology X) A
      (underlyingPresheaf (Opens.grothendieckTopology X) B)).obj x)) :
    ((stalkFunctor CommRingCat.{u} x).map
        (presentation (Opens.grothendieckTopology X) A B a E α).hom).hom
        (freeAlgebraStalkBackHom A B a E α x y) =
      ((stalkFunctor CommRingCat.{u} x).map
        (presentation (Opens.grothendieckTopology X) A B a
          (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _)).hom).hom y := by
  refine Eq.trans (DFunLike.congr_fun (stalkMap_presentation_comp_section A B a E α x)
    (freeAlgebraSheafStalkRingEquiv A (underlyingPresheaf (Opens.grothendieckTopology X) B) x y))
    ?_
  exact (stalkFunctor_map_presentation_apply A B a
    (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _) x y).symm

/-- The homomorphism `(A[B])ₓ → (A[E])ₓ` is a homomorphism of `Aₓ`-algebras. -/
theorem freeAlgebraStalkBackHom_coefficientMap (r : ToType (stalk A.obj x)) :
    freeAlgebraStalkBackHom A B a E α x
        (((stalkFunctor CommRingCat.{u} x).map
          (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A
            (underlyingPresheaf (Opens.grothendieckTopology X) B)).hom).hom r) =
      ((stalkFunctor CommRingCat.{u} x).map
        (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A E).hom).hom r := by
  refine Eq.trans (congrArg (MvPolynomial.eval₂Hom
      (((stalkFunctor CommRingCat.{u} x).map
        (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A E).hom).hom)
      (presentationStalkSection A B a E α x))
    (freeAlgebraSheafStalkRingEquiv_coefficientMap A
      (underlyingPresheaf (Opens.grothendieckTopology X) B) x r)) ?_
  exact MvPolynomial.eval₂Hom_C _ _ r

/-- **The stalk extension of an arbitrary presentation receives a morphism from the stalk
extension of the canonical one.** -/
def stalkExtensionHomBack :
    letI := stalkAlgebraBase A B a x
    (stalkExtension A (freeAlgebraSheaf (Opens.grothendieckTopology X) A
          (underlyingPresheaf (Opens.grothendieckTopology X) B)) B
        (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A
          (underlyingPresheaf (Opens.grothendieckTopology X) B))
        (presentation (Opens.grothendieckTopology X) A B a
          (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _)) a x
        (freeAlgebraSheafCoefficientMap_comp_desc (Opens.grothendieckTopology X) A B
          (underlyingPresheaf (Opens.grothendieckTopology X) B) a (𝟙 _))).Hom
      (stalkExtension A (freeAlgebraSheaf (Opens.grothendieckTopology X) A E) B
        (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A E)
        (presentation (Opens.grothendieckTopology X) A B a E α) a x
        (freeAlgebraSheafCoefficientMap_comp_desc (Opens.grothendieckTopology X) A B E a α)) :=
  letI := stalkAlgebraBase A B a x
  { toRingHom := freeAlgebraStalkBackHom A B a E α x
    toRingHom_algebraMap := freeAlgebraStalkBackHom_coefficientMap A B a E α x
    algebraMap_toRingHom := stalkMap_presentation_freeAlgebraStalkBackHom A B a E α x }

end Stacks.SheafOfModules

/-! ### The comparison map is a quasi-isomorphism -/

namespace Stacks.SheafOfModules

open Stacks.Sites.FreeAlgebra Stacks.Sites.Conormal
open AlgebraicGeometry.SheafOfModules (stalkFunctor)

variable {X : TopCat.{u}} (A B : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
  (a : A ⟶ B) (E : X.Presheaf (Type u))
  (α : E ⟶ Stacks.Sites.FreeAlgebra.underlyingPresheaf (Opens.grothendieckTopology X) B)
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
    (presentation (Opens.grothendieckTopology X) A B a E α).hom]

/-- For a morphism `a : A ⟶ B` of sheaves of commutative rings on a topological space and a
family of generators `α : E ⟶ B` presenting `B`, the canonical comparison map
`NL(α) ⟶ NL_{B/A}` is a quasi-isomorphism. -/
@[stacks 08TL]
theorem quasiIso_naiveCotangentComplexComparison :
    QuasiIso (naiveCotangentComplexComparison.{u, u, u, u}
      (Opens.grothendieckTopology X) A B a E α) := by
  change QuasiIso (presentationNaiveCotangentComplexMap.{u, u, u, u}
    (Opens.grothendieckTopology X) A E (underlyingPresheaf (Opens.grothendieckTopology X) B)
    α B a α (𝟙 _) (Category.comp_id α))
  refine (AlgebraicGeometry.SheafOfModules.quasiIso_iff_forall_stalk_quasiIso _ _).mpr fun x ↦ ?_
  let : (stalkFunctor (Tensor.ringSheaf B) x).Additive :=
    AlgebraicGeometry.SheafOfModules.stalkFunctor_additive (Tensor.ringSheaf B) x
  let : (stalkFunctor (Tensor.ringSheaf B) x).PreservesZeroMorphisms :=
    CategoryTheory.Functor.preservesZeroMorphisms_of_additive _
  let _ : DecidableEq (OrderDual (TopologicalSpace.OpenNhds x)) := Classical.decEq _
  let := stalkAlgebraBase A B a x
  let u₁ := (conormalSheafStalkLinearEquiv (freeAlgebraSheaf (Opens.grothendieckTopology X) A E) B
    (presentation (Opens.grothendieckTopology X) A B a E α) x).toAddEquiv
  let u₀ := (cotangentSpaceStalkLinearEquiv A (freeAlgebraSheaf (Opens.grothendieckTopology X) A E)
    B (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A E)
    (presentation (Opens.grothendieckTopology X) A B a E α) x).toAddEquiv
  let v₁ := (conormalSheafStalkLinearEquiv (freeAlgebraSheaf (Opens.grothendieckTopology X) A
    (underlyingPresheaf (Opens.grothendieckTopology X) B)) B
    (presentation (Opens.grothendieckTopology X) A B a
      (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _)) x).toAddEquiv
  let v₀ := (cotangentSpaceStalkLinearEquiv A (freeAlgebraSheaf (Opens.grothendieckTopology X) A
    (underlyingPresheaf (Opens.grothendieckTopology X) B)) B
    (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A
      (underlyingPresheaf (Opens.grothendieckTopology X) B))
    (presentation (Opens.grothendieckTopology X) A B a
      (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _)) x).toAddEquiv
  have hc₁ := freeAlgebraSheafCoefficientMap_comp_desc (Opens.grothendieckTopology X) A B E a α
  have hc₂ := freeAlgebraSheafCoefficientMap_comp_desc (Opens.grothendieckTopology X) A B
    (underlyingPresheaf (Opens.grothendieckTopology X) B) a (𝟙 _)
  have ha := freeAlgebraSheafCoefficientMap_comp_freeAlgebraMap (Opens.grothendieckTopology X) A E
    (underlyingPresheaf (Opens.grothendieckTopology X) B) α
  have hφ := freeAlgebraMap_comp_presentation (Opens.grothendieckTopology X) A E
    (underlyingPresheaf (Opens.grothendieckTopology X) B) α B a α (𝟙 _) (Category.comp_id α)
  have hqi := NaiveCotangent.nlExtensionMap_isQuasiIso
    (stalkExtensionHom A (freeAlgebraSheaf (Opens.grothendieckTopology X) A E)
      (freeAlgebraSheaf (Opens.grothendieckTopology X) A
        (underlyingPresheaf (Opens.grothendieckTopology X) B)) B
      (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A E)
      (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A
        (underlyingPresheaf (Opens.grothendieckTopology X) B))
      (presentation (Opens.grothendieckTopology X) A B a E α)
      (presentation (Opens.grothendieckTopology X) A B a
        (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _)) a
      (freeAlgebraMap (Opens.grothendieckTopology X) A E
        (underlyingPresheaf (Opens.grothendieckTopology X) B) α) x hc₁ hc₂ ha hφ)
    (stalkExtensionHomBack A B a E α x)
  have hdK := conormalSequenceStalkMapF_eq_cotangentComplex' A
    (freeAlgebraSheaf (Opens.grothendieckTopology X) A E) B
    (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A E)
    (presentation (Opens.grothendieckTopology X) A B a E α) x a hc₁
  have hdL := conormalSequenceStalkMapF_eq_cotangentComplex' A
    (freeAlgebraSheaf (Opens.grothendieckTopology X) A
      (underlyingPresheaf (Opens.grothendieckTopology X) B)) B
    (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A
      (underlyingPresheaf (Opens.grothendieckTopology X) B))
    (presentation (Opens.grothendieckTopology X) A B a
      (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _)) x a hc₂
  have hpc := conormalSheafMapOfFacStalk_eq_cotangentMap A
    (freeAlgebraSheaf (Opens.grothendieckTopology X) A E)
    (freeAlgebraSheaf (Opens.grothendieckTopology X) A
      (underlyingPresheaf (Opens.grothendieckTopology X) B)) B
    (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A E)
    (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A
      (underlyingPresheaf (Opens.grothendieckTopology X) B))
    (presentation (Opens.grothendieckTopology X) A B a E α)
    (presentation (Opens.grothendieckTopology X) A B a
      (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _))
    (freeAlgebraMap (Opens.grothendieckTopology X) A E
      (underlyingPresheaf (Opens.grothendieckTopology X) B) α) x hφ ha a hc₁ hc₂
  have hpt := tensorSheafMapOfFacStalk_eq_cotangentSpaceMap A
    (freeAlgebraSheaf (Opens.grothendieckTopology X) A E)
    (freeAlgebraSheaf (Opens.grothendieckTopology X) A
      (underlyingPresheaf (Opens.grothendieckTopology X) B)) B
    (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A E)
    (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A
      (underlyingPresheaf (Opens.grothendieckTopology X) B))
    (presentation (Opens.grothendieckTopology X) A B a E α)
    (presentation (Opens.grothendieckTopology X) A B a
      (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _))
    (freeAlgebraMap (Opens.grothendieckTopology X) A E
      (underlyingPresheaf (Opens.grothendieckTopology X) B) α) x hφ ha a hc₁ hc₂
  refine CochainComplex.quasiIso_of_isZero_X_of_eqToHom _ ?_ ?_
    ((stalkFunctor _ x).map
      (presentationConormalSequence.{u, u, u, u} (Opens.grothendieckTopology X) A B a E α).f)
    ((stalkFunctor _ x).map
      (presentationConormalSequence.{u, u, u, u} (Opens.grothendieckTopology X) A B a
        (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _)).f)
    ((stalkFunctor _ x).map
      (presentationConormalMap.{u, u, u, u} (Opens.grothendieckTopology X) A E
        (underlyingPresheaf (Opens.grothendieckTopology X) B) α B a α (𝟙 _) (Category.comp_id α)))
    ((stalkFunctor _ x).map
      (presentationTensorMap.{u, u, u, u} (Opens.grothendieckTopology X) A E
        (underlyingPresheaf (Opens.grothendieckTopology X) B) α B a α (𝟙 _) (Category.comp_id α)))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i h1 h2
    rw [Functor.mapHomologicalComplex_obj_X]
    exact AlgebraicGeometry.SheafOfModules.isZero_stalkFunctor_obj _ x _
      (presentationNaiveCotangentComplex_isZero_X (Opens.grothendieckTopology X) A B a E α i h1 h2)
  · intro i h1 h2
    rw [Functor.mapHomologicalComplex_obj_X]
    exact AlgebraicGeometry.SheafOfModules.isZero_stalkFunctor_obj _ x _
      (presentationNaiveCotangentComplex_isZero_X (Opens.grothendieckTopology X) A B a
        (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _) i h1 h2)
  · exact congrArg (stalkFunctor _ x).obj
      (presentationNaiveCotangentComplex_X_negOne (Opens.grothendieckTopology X) A B a E α)
  · exact congrArg (stalkFunctor _ x).obj
      (presentationNaiveCotangentComplex_X_zero (Opens.grothendieckTopology X) A B a E α)
  · exact congrArg (stalkFunctor _ x).obj
      (presentationNaiveCotangentComplex_X_negOne (Opens.grothendieckTopology X) A B a
        (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _))
  · exact congrArg (stalkFunctor _ x).obj
      (presentationNaiveCotangentComplex_X_zero (Opens.grothendieckTopology X) A B a
        (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _))
  · refine (Functor.mapHomologicalComplex_obj_d _ _ _ _ _).trans
      ((congrArg (stalkFunctor _ x).map
        (presentationNaiveCotangentComplex_d_negOne_zero (Opens.grothendieckTopology X)
          A B a E α)).trans (Functor.map_eqToHom_comp_comp_eqToHom _
        (presentationNaiveCotangentComplex_X_negOne (Opens.grothendieckTopology X) A B a E α) _
        (presentationNaiveCotangentComplex_X_zero (Opens.grothendieckTopology X) A B a E α)))
  · refine (Functor.mapHomologicalComplex_obj_d _ _ _ _ _).trans
      ((congrArg (stalkFunctor _ x).map
        (presentationNaiveCotangentComplex_d_negOne_zero (Opens.grothendieckTopology X)
          A B a (underlyingPresheaf (Opens.grothendieckTopology X) B)
          (𝟙 _))).trans (Functor.map_eqToHom_comp_comp_eqToHom _
        (presentationNaiveCotangentComplex_X_negOne (Opens.grothendieckTopology X) A B a
          (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _)) _
        (presentationNaiveCotangentComplex_X_zero (Opens.grothendieckTopology X) A B a
          (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _))))
  · refine (Functor.mapHomologicalComplex_map_f _ _ _ _).trans
      ((congrArg (stalkFunctor _ x).map
        (presentationNaiveCotangentComplexMap_f_negOne (Opens.grothendieckTopology X) A E
          (underlyingPresheaf (Opens.grothendieckTopology X) B) α B a α (𝟙 _)
          (Category.comp_id α))).trans (Functor.map_eqToHom_comp_comp_eqToHom _
        (presentationNaiveCotangentComplex_X_negOne (Opens.grothendieckTopology X) A B a E α) _
        (presentationNaiveCotangentComplex_X_negOne (Opens.grothendieckTopology X) A B a
          (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _))))
  · refine (Functor.mapHomologicalComplex_map_f _ _ _ _).trans
      ((congrArg (stalkFunctor _ x).map
        (presentationNaiveCotangentComplexMap_f_zero (Opens.grothendieckTopology X) A E
          (underlyingPresheaf (Opens.grothendieckTopology X) B) α B a α (𝟙 _)
          (Category.comp_id α))).trans (Functor.map_eqToHom_comp_comp_eqToHom _
        (presentationNaiveCotangentComplex_X_zero (Opens.grothendieckTopology X) A B a E α) _
        (presentationNaiveCotangentComplex_X_zero (Opens.grothendieckTopology X) A B a
          (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _))))
  · exact CochainComplex.eq_zero_of_d_eq_zero_of_addEquiv (u₁ := u₁) (u₀ := u₀) (v₁ := v₁)
      hdK hpc hqi.eq_zero_of_d_eq_zero
  · exact CochainComplex.exists_of_d_eq_zero_of_addEquiv (u₁ := u₁) (u₀ := u₀) (v₁ := v₁)
      (v₀ := v₀) hdK hdL hpc hqi.exists_of_d_eq_zero
  · exact CochainComplex.exists_d_eq_of_addEquiv (u₁ := u₁) (u₀ := u₀) (v₁ := v₁) (v₀ := v₀)
      hdK hdL hpt hqi.exists_d_eq
  · exact CochainComplex.exists_add_d_eq_of_addEquiv (u₀ := u₀) (v₁ := v₁) (v₀ := v₀)
      hdL hpt hqi.exists_add_d_eq

end Stacks.SheafOfModules

end

end
