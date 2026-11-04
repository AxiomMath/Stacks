module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedAxiomA
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedTensorHomAdjunction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The hom-complex form of the tensor-hom adjunction for sheaves of differential graded modules

Let `X` be a ringed site, let `A` and `B` be sheaves of differential graded algebras on it, let
`M` be a right differential graded `A`-module, let `N` be a differential graded
`(A, B)`-bimodule and let `L` be a right differential graded `B`-module. Writing `T` for the
tensor product `M ⊗_A N` and `H` for the internal hom `SheafHom^dg_B(N, L)`, the first displayed
identity of the source is

`Hom_{Mod^dg(B, d)}(M ⊗_A N, L) = Hom_{Mod^dg(A, d)}(M, SheafHom^dg_B(N, L))`,

an equality of the hom-complexes of the two differential graded categories of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedAxiomA.lean`. This file proves
it: the degree-`n` homogeneous morphisms correspond, and the correspondence commutes with the
differential of the hom-complexes.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.LocalHomFamily` is a family of degree-`n` local
  homomorphisms, one over every object of the site, compatible with restriction;
  `SheafOfModules.DifferentialGradedModule.HomogeneousMap.localHomFamily` and
  `SheafOfModules.DifferentialGradedModule.LocalHomFamily.cochain` are the two directions of the
  dictionary between such families and the homogeneous right-linear maps of degree `n`.
* `SheafOfModules.DifferentialGradedModule.tensorHomHomogeneousEquiv` is the first displayed
  identity on homogeneous morphisms: the degree-`n` homogeneous right-linear maps
  `M ⊗_A N → L` are the degree-`n` homogeneous right-linear maps `M → SheafHom^dg_B(N, L)`.
* `SheafOfModules.DifferentialGradedModule.dgHomEquiv` is the same identity read in the
  differential graded categories themselves.

## Main results

* `SheafOfModules.DifferentialGradedModule.homogeneousEquiv_add`: the identity is additive, so
  it identifies each degree of the two hom-complexes as an abelian group.
* `SheafOfModules.DifferentialGradedModule.homogeneousEquiv_delta` and
  `SheafOfModules.DifferentialGradedModule.dgHomEquiv_d`: the identity commutes with the
  differential of the hom-complexes, which is the differential graded content of the first
  displayed identity.
* `SheafOfModules.DifferentialGradedModule.homogeneousEquiv_sectionsEquiv_app`: the identity is
  `φ ↦ (x ↦ (y ↦ φ (x ⊗ y)))` on local sections.
* `SheafOfModules.DifferentialGradedModule.homogeneousEquiv_naturality_left`,
  `SheafOfModules.DifferentialGradedModule.homogeneousEquiv_naturality_right` and
  `SheafOfModules.DifferentialGradedModule.homogeneousEquiv_naturality_bimodule` are the
  source's functoriality of the first identity in `M`, in `L` and in `N`.
* `SheafOfModules.DifferentialGradedModule.LocalHomFamily.localHomFamily_cochain` and
  `SheafOfModules.DifferentialGradedModule.HomogeneousMap.cochain_localHomFamily`: a homogeneous
  right-linear map of degree `n` is the same datum as a compatible family of degree-`n` local
  homomorphisms.

## Implementation notes

A homogeneous morphism of the differential graded category `Mod^dg(A, d)` is a
`SheafOfModules.DifferentialGradedModule.HomogeneousMap`, an action-linear cochain of the
underlying complexes of sheaves of modules, and the differential of the hom-complex is the
commutator `CochainComplex.HomComplex.δ`; that is how
`SheafOfModules.DifferentialGradedModule.dgCategoryData` builds the differential graded
category, so the identity is stated for those and then transported to the category itself
through `SheafOfModules.DifferentialGradedModule.moduleHomEquiv`.

The second displayed identity, between two internal homs, is proved in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedTensorHomAdjunction.lean`, whose
local material is what the proof here runs on: a homogeneous morphism out of a tensor product is
the same as a compatible family of local homomorphisms out of it, hence of `A`-balanced bilinear
families, hence of local homomorphisms into the internal hom
(`SheafOfModules.balancedEquivDg`). The differential is the one point that the local material
does not already give, since the hom-complex differential is a commutator of cochains and not
the differential of a complex of sheaves whose sections are pinned; it is computed here from
`CochainComplex.HomComplex.δ_v` and the signed Leibniz rule
`SheafOfModules.IsTensorProduct.tmul_d_castHom` of the tensor product.

Neither the tensor product nor the internal hom can be written down over a general ringed site,
so both are used through the predicates `SheafOfModules.IsTensorProduct` and
`SheafOfModules.IsSheafHom`, exactly as for the second identity. The hypotheses `hT` and `hH`
are therefore not extra inputs: each says only that the object it is given *is* one of the two
constructions the source's statement names, and the source's own hypotheses — a ringed site,
two sheaves of differential graded algebras `A` and `B`, a right module `M`, a bimodule `N` and
a right module `L` — are the variables above. The identity is proved for every object with the
universal property, so it holds in particular for the source's `M ⊗_A N` and
`SheafHom^dg_B(N, L)`.

The hypotheses `hχ` and `hψ` of `homogeneousEquiv_add` and `homogeneousEquiv_delta` name the
sum and the differential of the given homogeneous morphisms; both are realized, by the
`AddCommGroup` structure on `SheafOfModules.DifferentialGradedModule.HomogeneousMap` and by
`SheafOfModules.DifferentialGradedModule.underlyingCochain_d`, so they restrict nothing either.

The base is a ringed site rather than an arbitrary sheaf of rings on a site, because
`SheafOfModules.DifferentialGradedModule.HomogeneousMap` and the differential graded category it
belongs to are defined over a ringed site, whose structure sheaf supplies the commutative ground
ring that `DGCategory` needs. The module universes of the `A`-side and of the `B`-side and the
universe of the bimodule are independent; `M` and `H` share a universe, as do `T` and `L`,
because each pair is the source and target of one hom-complex.

Additivity is stated for `tensorHomHomogeneousEquiv`, at the level of the action-linear
cochains, and not for `dgHomEquiv`: a `DGCategoryData` identifies its homogeneous morphisms
with the action-linear cochains as *types*, so nothing in it ties the addition of its
hom-groups to the addition of cochains, and additivity of `dgHomEquiv` is therefore not a
statement about the chosen datum that could be proved. Linearity over the ring of global
sections is not stated at all, for the same reason on the one side and because the module
structure on the cochains is internal to
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedAxiomA.lean` on the other.

The source's `functorially in M, N, L` is the naturality section at the end of the file. A
morphism in one of the three variables induces one between the tensor products or one between
the internal homs, and the identification of the hom-complexes carries composition with the one
to composition with the other. Those induced morphisms cannot be written by a formula over a
general ringed site any more than the objects can, so each is taken as a morphism together with
the hypothesis pinning it on local sections, exactly as the objects are taken with the
predicates that pin them; `ht` is `SheafOfModules.TensorFunctorData.map_spec` and the `hg` of
`SheafOfModules.DifferentialGradedModule.homogeneousEquiv_naturality_right` is
`SheafOfModules.SheafHomFunctorData.map_spec`, both verbatim, so they are realized and restrict
nothing. The hypotheses `hφ`, `hφ'` name the composite cochain whose image is asserted, in the
same way as the `hχ` and `hψ` above, and are realized by `CochainComplex.HomComplex.Cochain.comp`
with `CochainComplex.HomComplex.Cochain.ofHom`.

Naturality is stated at the level of the action-linear cochains and not for `dgHomEquiv`, for
the reason additivity is: a `DGCategoryData` identifies its homogeneous morphisms with the
cochains as types only, so composition in it is tied to composition of cochains by
`SheafOfModules.DifferentialGradedModule.underlyingCochain_comp`, and the cochain statement is
what that lemma reduces a statement about the category to.

## References

* [Stacks Project, Tag 0FRS](https://stacks.math.columbia.edu/tag/0FRS)
* [Stacks Project, Tag 0FR6](https://stacks.math.columbia.edu/tag/0FR6)
* [Stacks Project, Tag 0FRN](https://stacks.math.columbia.edu/tag/0FRN)
* [Stacks Project, Tag 0FS4](https://stacks.math.columbia.edu/tag/0FS4)
-/

@[expose] public section

open CategoryTheory

universe u v w z s

namespace SheafOfModules.DifferentialGradedModule

open CochainComplex.HomComplex

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}

/-! ### Homogeneous morphisms as compatible families of local homomorphisms -/

section Family

variable {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
  {K L : DifferentialGradedModule.{u, v, w} A} {n : ℤ}

/-- The degree-`n` local homomorphism `K|_U → L|_U` that a homogeneous right-linear map of
degree `n` gives over an object `U` of the site. -/
noncomputable def HomogeneousMap.localHom (f : HomogeneousMap A K L n) (U : X.C) :
    LocalHom K L n U where
  app i j hij V := homSections (f.val.v i j hij) (Opposite.op V.left)
  map_smul _ _ _ _ r x := homSections_smul _ _ r x
  naturality _ _ _ _ _ _ _ := homSections_naturality _ _ _
  isLinear i j hij p V x b := eq_of_heq (f.property i j p hij (Opposite.op V.left) x b)

/-- The local homomorphism of a homogeneous map over `U` acts on sections over `V` by the
component of the map on sections over `V.left`. -/
@[simp]
theorem HomogeneousMap.localHom_app (f : HomogeneousMap A K L n) (U : X.C) (i j : ℤ)
    (hij : i + n = j) (V : Over U) (x : (K.complex.X i).val.obj (Opposite.op V.left)) :
    (f.localHom U).app i j hij V x = homSections (f.val.v i j hij) (Opposite.op V.left) x := rfl

/-- Restricting the local homomorphism of a homogeneous map along `U' ⟶ U` gives its local
homomorphism over `U'`. -/
theorem HomogeneousMap.localHom_restrict (f : HomogeneousMap A K L n) {U U' : X.C}
    (g : U' ⟶ U) : (f.localHom U).restrict g = f.localHom U' := rfl

/-- A family of degree-`n` local homomorphisms `K|_U → L|_U`, one over every object of the site,
compatible with restriction. This is the datum of a homogeneous right-linear map of degree
`n`. -/
@[ega "II 2.1.2" "more general"]
structure LocalHomFamily
    {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (K L : DifferentialGradedModule.{u, v, w} A) (n : ℤ) where
  /-- The local homomorphism over an object of the site. -/
  hom (U : X.C) : LocalHom K L n U
  /-- The local homomorphisms are compatible with restriction. -/
  restrict {U U' : X.C} (g : U' ⟶ U) : (hom U).restrict g = hom U'

/-- A family of local homomorphisms is determined by its members. -/
@[ext]
theorem LocalHomFamily.ext {F G : LocalHomFamily K L n} (h : ∀ U : X.C, F.hom U = G.hom U) :
    F = G := by
  cases F with
  | mk f hf =>
    cases G with
    | mk g hg =>
      obtain rfl : f = g := funext h
      rfl

/-- A homogeneous right-linear map of degree `n`, read as a compatible family of degree-`n`
local homomorphisms. -/
noncomputable def HomogeneousMap.localHomFamily (f : HomogeneousMap A K L n) :
    LocalHomFamily K L n where
  hom := f.localHom
  restrict := f.localHom_restrict

/-- The morphism of sheaves of modules from degree `i` to degree `j` assembled from a compatible
family of degree-`n` local homomorphisms. -/
noncomputable def LocalHomFamily.component (F : LocalHomFamily K L n) (i j : ℤ) (hij : i + n = j) :
    K.complex.X i ⟶ L.complex.X j where
  val :=
    { app := fun U => ModuleCat.ofHom
        { toFun := fun x => (F.hom U.unop).app i j hij (Over.mk (𝟙 U.unop)) x
          map_add' := fun x y => map_add _ x y
          map_smul' := fun r x =>
            (F.hom U.unop).map_smul i j hij (Over.mk (𝟙 U.unop)) r x }
      naturality := fun {U V} γ => by
        refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
        refine Eq.symm (((F.hom U.unop).naturality i j hij
          (Over.homMk γ.unop (Category.comp_id γ.unop) :
            Over.mk γ.unop ⟶ Over.mk (𝟙 U.unop)) x).trans ?_)
        refine ((F.hom U.unop).toLocalGradedHom.app_mk_congr i j hij
          (Category.id_comp γ.unop).symm _).trans ?_
        exact LocalHom.app_congr (F.restrict γ.unop) i j hij (Over.mk (𝟙 V.unop)) _ }

/-- On sections over `U`, the assembled component is the member of the family over `U` evaluated
over the identity of `U`. -/
@[simp]
theorem LocalHomFamily.component_apply (F : LocalHomFamily K L n) (i j : ℤ) (hij : i + n = j)
    (U : X.Cᵒᵖ) (x : (K.complex.X i).val.obj U) :
    homSections (F.component i j hij) U x =
      (F.hom U.unop).app i j hij (Over.mk (𝟙 U.unop)) x := rfl

/-- The homogeneous right-linear map of degree `n` assembled from a compatible family of
degree-`n` local homomorphisms. -/
noncomputable def LocalHomFamily.cochain (F : LocalHomFamily K L n) : HomogeneousMap A K L n :=
  ⟨Cochain.mk fun i j hij => F.component i j hij, fun i j p hij U x b =>
    heq_of_eq ((F.hom U.unop).isLinear i j hij p (Over.mk (𝟙 U.unop)) x b)⟩

/-- The components of the homogeneous map assembled from a family are the morphisms
`LocalHomFamily.component`. -/
@[simp]
theorem LocalHomFamily.cochain_val_v (F : LocalHomFamily K L n) (i j : ℤ) (hij : i + n = j) :
    F.cochain.val.v i j hij = F.component i j hij := rfl

/-- The local homomorphism over `U` of the homogeneous map assembled from a family is the member
of the family over `U`. -/
theorem LocalHomFamily.localHom_cochain (F : LocalHomFamily K L n) (U : X.C) :
    F.cochain.localHom U = F.hom U := by
  refine LocalHom.ext fun i j hij V x => ?_
  refine (LocalHom.app_congr (F.restrict V.hom) i j hij (Over.mk (𝟙 V.left)) x).symm.trans ?_
  exact (F.hom U).toLocalGradedHom.app_mk_congr i j hij (Category.id_comp V.hom) x

/-- Reading the homogeneous map assembled from a family back as a family recovers the family. -/
theorem LocalHomFamily.localHomFamily_cochain (F : LocalHomFamily K L n) :
    F.cochain.localHomFamily = F :=
  LocalHomFamily.ext F.localHom_cochain

/-- Assembling the family of local homomorphisms of a homogeneous map recovers the map. -/
theorem HomogeneousMap.cochain_localHomFamily (f : HomogeneousMap A K L n) :
    f.localHomFamily.cochain = f := by
  refine Subtype.ext (Cochain.ext _ _ fun i j hij => ?_)
  exact SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
    ModuleCat.hom_ext (LinearMap.ext fun x => rfl))

/-- The differential of the differential graded category of right differential graded modules
is the commutator differential on the underlying action-linear cochains. -/
theorem underlyingCochain_d (D : DGCategoryData.{u, v, w} A) {n : ℤ}
    (f : D.category.Hom (moduleObject A D K) (moduleObject A D L) n) :
    underlyingCochain A D (D.category.d f) = δ n (n + 1) (underlyingCochain A D f) := by
  show (D.homs K L (n + 1) ▸ D.category.d f).val = _
  rw [eq_of_heq (D.differential K L n f)]
  rfl

end Family

/-! ### The first displayed identity on homogeneous morphisms -/

section FirstIdentity

variable {A B : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
  {M H : DifferentialGradedModule.{u, v, w} A}
  {N : DifferentialGradedBimodule.{u, v, z} A B}
  {L T : DifferentialGradedModule.{u, v, s} B}

/-- A compatible family of degree-`n` local homomorphisms out of the tensor product `M ⊗_A N`,
read as a compatible family of degree-`n` local homomorphisms into the internal hom
`SheafHom^dg_B(N, L)`. -/
noncomputable def tensorFamily (hT : IsTensorProduct M N T) (hH : IsSheafHom N L H) (n : ℤ)
    (F : LocalHomFamily T L n) : LocalHomFamily M H n where
  hom U := ofBalancedDg hH (hT.universal L n U (F.hom U))
  restrict {U U'} g := by
    rw [ofBalancedDg_restrict]
    refine congrArg (ofBalancedDg hH) (LocalBalancedBilinear.ext fun i j k hijk V x y => ?_)
    rw [LocalBalancedBilinear.restrict_app, ← F.restrict g,
      hT.universal_restrict L n g (F.hom U) i j k hijk V x y]

/-- A compatible family of degree-`n` local homomorphisms into the internal hom
`SheafHom^dg_B(N, L)`, read as a compatible family of degree-`n` local homomorphisms out of the
tensor product `M ⊗_A N`. -/
noncomputable def sheafHomFamily (hT : IsTensorProduct M N T) (hH : IsSheafHom N L H) (n : ℤ)
    (G : LocalHomFamily M H n) : LocalHomFamily T L n where
  hom U := (hT.universal L n U).symm (toBalancedDg hH (G.hom U))
  restrict {U U'} g := by
    rw [hT.universal_symm_restrict L n g, toBalancedDg_restrict, G.restrict]

/-- The two readings of a compatible family of local homomorphisms are inverse to one
another. -/
theorem tensorFamily_sheafHomFamily (hT : IsTensorProduct M N T) (hH : IsSheafHom N L H) (n : ℤ)
    (G : LocalHomFamily M H n) : tensorFamily hT hH n (sheafHomFamily hT hH n G) = G := by
  refine LocalHomFamily.ext fun U => ?_
  show ofBalancedDg hH
    (hT.universal L n U ((hT.universal L n U).symm (toBalancedDg hH (G.hom U)))) = G.hom U
  rw [Equiv.apply_symm_apply, ofBalancedDg_toBalancedDg]

/-- The two readings of a compatible family of local homomorphisms are inverse to one
another. -/
theorem sheafHomFamily_tensorFamily (hT : IsTensorProduct M N T) (hH : IsSheafHom N L H) (n : ℤ)
    (F : LocalHomFamily T L n) : sheafHomFamily hT hH n (tensorFamily hT hH n F) = F := by
  refine LocalHomFamily.ext fun U => ?_
  show (hT.universal L n U).symm
    (toBalancedDg hH (ofBalancedDg hH (hT.universal L n U (F.hom U)))) = F.hom U
  rw [toBalancedDg_ofBalancedDg, Equiv.symm_apply_apply]

/-- **Tensor-hom adjunction for sheaves of differential graded modules**, first identity, in a
fixed degree: the degree-`n` homogeneous right-linear maps `M ⊗_A N → L` of right differential
graded `B`-modules are the degree-`n` homogeneous right-linear maps
`M → SheafHom^dg_B(N, L)` of right differential graded `A`-modules. -/
@[stacks 0FRS "Hom_{Mod^dg(B, d)}(M ⊗_A N, L) = Hom_{Mod^dg(A, d)}(M, SheafHom^dg_B(N, L))
as hom-complexes: degreewise, additively, and compatibly with the differentials"]
noncomputable def tensorHomHomogeneousEquiv (hT : IsTensorProduct M N T) (hH : IsSheafHom N L H)
    (n : ℤ) : HomogeneousMap B T L n ≃ HomogeneousMap A M H n where
  toFun φ := (tensorFamily hT hH n φ.localHomFamily).cochain
  invFun ψ := (sheafHomFamily hT hH n ψ.localHomFamily).cochain
  left_inv φ := by
    dsimp only
    rw [LocalHomFamily.localHomFamily_cochain, sheafHomFamily_tensorFamily,
      HomogeneousMap.cochain_localHomFamily]
  right_inv ψ := by
    dsimp only
    rw [LocalHomFamily.localHomFamily_cochain, tensorFamily_sheafHomFamily,
      HomogeneousMap.cochain_localHomFamily]

/-- The identity sends a homogeneous right-linear map `φ` out of the tensor product to
`x ↦ (y ↦ φ (x ⊗ y))` on local sections. -/
theorem homogeneousEquiv_sectionsEquiv_app (hT : IsTensorProduct M N T) (hH : IsSheafHom N L H)
    (n : ℤ) (φ : HomogeneousMap B T L n) (p q : ℤ) (hpq : p + n = q) (U : X.C)
    (x : (M.complex.X p).val.obj (Opposite.op U)) (j k : ℤ) (hjk : j + q = k) (W : Over U)
    (y : (N.toRightModule.complex.X j).val.obj (Opposite.op W.left)) :
    (hH.isInternalHom.sectionsEquiv q U
        (homSections ((tensorHomHomogeneousEquiv hT hH n φ).val.v p q hpq) (Opposite.op U) x)).app
          j k hjk W y =
      homSections (φ.val.v (p + j) k (by omega)) (Opposite.op W.left)
        (hT.tmul p j (Opposite.op W.left) ((M.complex.X p).val.map W.hom.op x) y) := by
  have hval : homSections ((tensorHomHomogeneousEquiv hT hH n φ).val.v p q hpq) (Opposite.op U) x =
      (ofBalancedDg hH (hT.universal L n U (φ.localHom U))).app p q hpq (Over.mk (𝟙 U)) x := rfl
  rw [hval]
  exact (ofBalancedDg_sectionsEquiv_app hH (hT.universal L n U (φ.localHom U)) p q hpq
      (Over.mk (𝟙 U)) x j k hjk W y).trans
    (hT.universal_app L n U (φ.localHom U) p j k (by omega)
      (Over.mk (W.hom ≫ (Over.mk (𝟙 U)).hom)) _ y)

/-! ### The differential -/

section Delta

private theorem homSections_zsmul
    {S S' : SheafOfModules.{s} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (r : ℤ) (f : S ⟶ S')
    (U : X.Cᵒᵖ) (x : S.val.obj U) :
    homSections (r • f) U x = r • homSections f U x :=
  sheaf_hom_app_zsmul r f U x

private theorem homSections_v_castHom
    {P Q : CochainComplex (SheafOfModules.{s} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    {m : ℤ} (γ : Cochain P Q m)
    {i i' j : ℤ} (h : i = i') (hij : i' + m = j) (U : X.Cᵒᵖ) (x : (P.X i).val.obj U) :
    homSections (γ.v i' j hij) U (castHom P.X h U x) =
      homSections (γ.v i j (by omega)) U x := by
  subst h; rfl

/-- The value on local sections of the commutator differential of the hom-complex, computed
through arbitrary presentations of the two intermediate degrees. -/
private theorem homSections_delta_v
    {P Q : CochainComplex (SheafOfModules.{s} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    {m : ℤ} (γ : Cochain P Q m)
    (p q q₁ q₂ : ℤ) (hpq : p + (m + 1) = q) (hq₁ : q₁ = q - 1) (hq₂ : p + 1 = q₂)
    (U : X.Cᵒᵖ) (x : (P.X p).val.obj U) :
    homSections ((δ m (m + 1) γ).v p q hpq) U x =
      (Q.d q₁ q).val.app U (homSections (γ.v p q₁ (by omega)) U x) +
        ((m + 1).negOnePow : ℤ) •
          homSections (γ.v q₂ q (by omega)) U ((P.d p q₂).val.app U x) := by
  rw [δ_v m (m + 1) rfl γ p q hpq q₁ q₂ hq₁ hq₂, homSections_add, Units.smul_def,
    homSections_zsmul, homSections_comp, homSections_comp]
  rfl

/-- Sections of the precomposition of a cochain with a morphism of complexes. -/
private theorem homSections_ofHom_comp_v
    {P Q R : CochainComplex (SheafOfModules.{s} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (e : P ⟶ Q) {m : ℤ} (γ : Cochain Q R m) (i j : ℤ) (hij : i + m = j) (V : X.Cᵒᵖ)
    (z : (P.X i).val.obj V) :
    homSections (((Cochain.ofHom e).comp γ (zero_add m)).v i j hij) V z =
      homSections (γ.v i j hij) V ((e.f i).val.app V z) := by
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, homSections_comp]
  rfl

/-- Sections of the postcomposition of a cochain with a morphism of complexes. -/
private theorem homSections_comp_ofHom_v
    {P Q R : CochainComplex (SheafOfModules.{s} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    {m : ℤ} (γ : Cochain P Q m) (e : Q ⟶ R) (i j : ℤ) (hij : i + m = j) (V : X.Cᵒᵖ)
    (z : (P.X i).val.obj V) :
    homSections ((γ.comp (Cochain.ofHom e) (add_zero m)).v i j hij) V z =
      (e.f j).val.app V (homSections (γ.v i j hij) V z) := by
  rw [Cochain.comp_zero_cochain_v, Cochain.ofHom_v, homSections_comp]
  rfl

end Delta

/-- **Tensor-hom adjunction for sheaves of differential graded modules**, first identity, on
the additions: the identification of the homogeneous morphisms is additive, so each degree of
the two hom-complexes is identified as an abelian group. -/
@[stacks 0FRS "Hom_{Mod^dg(B, d)}(M ⊗_A N, L) = Hom_{Mod^dg(A, d)}(M, SheafHom^dg_B(N, L))
as hom-complexes: degreewise, additively, and compatibly with the differentials"]
theorem homogeneousEquiv_add (hT : IsTensorProduct M N T) (hH : IsSheafHom N L H) (n : ℤ)
    (φ φ' χ : HomogeneousMap B T L n) (hχ : χ.val = φ.val + φ'.val) :
    (tensorHomHomogeneousEquiv hT hH n χ).val =
      (tensorHomHomogeneousEquiv hT hH n φ).val + (tensorHomHomogeneousEquiv hT hH n φ').val := by
  refine Cochain.ext _ _ fun p q hpq => homSections_ext fun U x => ?_
  obtain ⟨U⟩ := U
  refine hH.isInternalHom.sections_ext fun j k hjk W y => ?_
  rw [homogeneousEquiv_sectionsEquiv_app hT hH n χ p q hpq U x j k hjk W y, hχ]
  simp only [Cochain.add_v, homSections_add]
  rw [hH.isInternalHom.sectionsEquiv_add q U _ _ j k hjk W y,
    homogeneousEquiv_sectionsEquiv_app hT hH n φ p q hpq U x j k hjk W y,
    homogeneousEquiv_sectionsEquiv_app hT hH n φ' p q hpq U x j k hjk W y]

/-- **Tensor-hom adjunction for sheaves of differential graded modules**, first identity, on
the differentials: the identification of the homogeneous morphisms commutes with the commutator
differential of the two hom-complexes. -/
@[stacks 0FRS "Hom_{Mod^dg(B, d)}(M ⊗_A N, L) = Hom_{Mod^dg(A, d)}(M, SheafHom^dg_B(N, L))
as hom-complexes: degreewise, additively, and compatibly with the differentials"]
theorem homogeneousEquiv_delta (hT : IsTensorProduct M N T) (hH : IsSheafHom N L H) (n : ℤ)
    (φ : HomogeneousMap B T L n) (ψ : HomogeneousMap B T L (n + 1))
    (hψ : ψ.val = δ n (n + 1) φ.val) :
    (tensorHomHomogeneousEquiv hT hH (n + 1) ψ).val =
      δ n (n + 1) (tensorHomHomogeneousEquiv hT hH n φ).val := by
  refine Cochain.ext _ _ fun p q hpq => homSections_ext fun U x => ?_
  obtain ⟨U⟩ := U
  obtain rfl : q = p + n + 1 := by omega
  refine hH.isInternalHom.sections_ext fun j k hjk W y => ?_
  rw [homogeneousEquiv_sectionsEquiv_app hT hH (n + 1) ψ p (p + n + 1) hpq U x j k hjk W y,
    homSections_delta_v (tensorHomHomogeneousEquiv hT hH n φ).val p (p + n + 1) (p + n) (p + 1)
      (by omega) (by omega) (by omega) (Opposite.op U) x,
    hH.isInternalHom.sectionsEquiv_add (p + n + 1) U _ _ j k hjk W y,
    hH.isInternalHom.sectionsEquiv_zsmul (p + n + 1) U _ _ j k hjk W y,
    hH.isInternalHom.sectionsEquiv_d (p + n) (p + n + 1) U
      (homSections ((tensorHomHomogeneousEquiv hT hH n φ).val.v p (p + n) rfl) (Opposite.op U) x)
      j k hjk W y,
    localDiffApp_eq (hH.isInternalHom.sectionsEquiv (p + n) U
        (homSections ((tensorHomHomogeneousEquiv hT hH n φ).val.v p (p + n) rfl)
          (Opposite.op U) x)).toLocalGradedHom
      (p + n + 1) j k (p + j + n) (j + 1) hjk (by omega) (by omega) W y]
  rw [homogeneousEquiv_sectionsEquiv_app hT hH n φ p (p + n) rfl U x j (p + j + n) (by omega) W y,
    homogeneousEquiv_sectionsEquiv_app hT hH n φ p (p + n) rfl U x (j + 1) k (by omega) W
      ((N.toRightModule.complex.d j (j + 1)).val.app (Opposite.op W.left) y),
    homogeneousEquiv_sectionsEquiv_app hT hH n φ (p + 1) (p + n + 1) (by omega) U
      ((M.complex.d p (p + 1)).val.app (Opposite.op U) x) j k (by omega) W y]
  simp only [DifferentialGradedBimodule.toRightModule_complex]
  have hdnat : (M.complex.X (p + 1)).val.map W.hom.op
        ((M.complex.d p (p + 1)).val.app (Opposite.op U) x) =
      (M.complex.d p (p + 1)).val.app (Opposite.op W.left)
        ((M.complex.X p).val.map W.hom.op x) :=
    homSections_naturality (M.complex.d p (p + 1)) W.hom.op x
  rw [hdnat,
    hψ,
    homSections_delta_v φ.val (p + j) k (p + j + n) (p + j + 1) (by omega) (by omega)
      (by omega) (Opposite.op W.left) _,
    hT.tmul_d_castHom p j (Opposite.op W.left) ((M.complex.X p).val.map W.hom.op x) y,
    map_add, map_zsmul, homSections_v_castHom φ.val (add_right_comm p 1 j) (by omega),
    homSections_v_castHom φ.val (add_assoc p j 1).symm (by omega)]
  simp only
  rw [smul_add, smul_smul, ← Units.val_mul, ← Int.negOnePow_add,
    show n + 1 + p = p + n + 1 from by omega]
  abel

/-! ### The first displayed identity in the differential graded categories -/

/-- **Tensor-hom adjunction for sheaves of differential graded modules**, first identity: the
degree-`n` homogeneous morphisms `M ⊗_A N → L` of the differential graded category
`Mod^dg(B, d)` are the degree-`n` homogeneous morphisms `M → SheafHom^dg_B(N, L)` of the
differential graded category `Mod^dg(A, d)`. -/
@[stacks 0FRS "Hom_{Mod^dg(B, d)}(M ⊗_A N, L) = Hom_{Mod^dg(A, d)}(M, SheafHom^dg_B(N, L))
as hom-complexes: degreewise, additively, and compatibly with the differentials"]
noncomputable def dgHomEquiv (hT : IsTensorProduct M N T) (hH : IsSheafHom N L H) (n : ℤ) :
    (dgCategoryData B).category.Hom (moduleObject B (dgCategoryData B) T)
        (moduleObject B (dgCategoryData B) L) n ≃
      (dgCategoryData A).category.Hom (moduleObject A (dgCategoryData A) M)
        (moduleObject A (dgCategoryData A) H) n :=
  (moduleHomEquiv B (dgCategoryData B) T L n).trans
    ((tensorHomHomogeneousEquiv hT hH n).trans (moduleHomEquiv A (dgCategoryData A) M H n).symm)

/-- **Tensor-hom adjunction for sheaves of differential graded modules**, first identity: the
identification of the two hom-complexes commutes with their differentials, so it is an equality
of complexes and not only of their degreewise components. -/
@[stacks 0FRS "Hom_{Mod^dg(B, d)}(M ⊗_A N, L) = Hom_{Mod^dg(A, d)}(M, SheafHom^dg_B(N, L))
as hom-complexes: degreewise, additively, and compatibly with the differentials"]
theorem dgHomEquiv_d (hT : IsTensorProduct M N T) (hH : IsSheafHom N L H) (n : ℤ)
    (f : (dgCategoryData B).category.Hom (moduleObject B (dgCategoryData B) T)
      (moduleObject B (dgCategoryData B) L) n) :
    (dgCategoryData A).category.d (dgHomEquiv hT hH n f) =
      dgHomEquiv hT hH (n + 1) ((dgCategoryData B).category.d f) := by
  apply underlyingCochain_injective A (dgCategoryData A)
  rw [underlyingCochain_d]
  have hφ : underlyingCochain A (dgCategoryData A) (dgHomEquiv hT hH n f) =
      (tensorHomHomogeneousEquiv hT hH n (moduleHomEquiv B (dgCategoryData B) T L n f)).val :=
    congrArg Subtype.val ((moduleHomEquiv A (dgCategoryData A) M H n).apply_symm_apply _)
  have hψ : underlyingCochain A (dgCategoryData A)
        (dgHomEquiv hT hH (n + 1) ((dgCategoryData B).category.d f)) =
      (tensorHomHomogeneousEquiv hT hH (n + 1) (moduleHomEquiv B (dgCategoryData B) T L (n + 1)
        ((dgCategoryData B).category.d f))).val :=
    congrArg Subtype.val ((moduleHomEquiv A (dgCategoryData A) M H (n + 1)).apply_symm_apply _)
  rw [hφ, hψ]
  exact (homogeneousEquiv_delta hT hH n _ _ (underlyingCochain_d (dgCategoryData B) f)).symm

/-! ### Functoriality of the first displayed identity -/

section Naturality

variable {M' H' : DifferentialGradedModule.{u, v, w} A}
  {N' : DifferentialGradedBimodule.{u, v, z} A B}
  {L' T' : DifferentialGradedModule.{u, v, s} B}

/-- **Tensor-hom adjunction for sheaves of differential graded modules**, first identity,
functoriality in `M`: a morphism `u : M' ⟶ M` of right differential graded `A`-modules induces
`t : M' ⊗_A N ⟶ M ⊗_A N`, and the identification of the hom-complexes carries precomposition
with `t` to precomposition with `u`. -/
@[stacks 0FRS "functoriality of the hom-complex identity in M: a morphism M' ⟶ M compatible \
with the tensor products carries the identification at M to the one at M'"]
theorem homogeneousEquiv_naturality_left (hT : IsTensorProduct M N T)
    (hT' : IsTensorProduct M' N T') (hH : IsSheafHom N L H) (u : M' ⟶ M) (t : T' ⟶ T)
    (ht : ∀ (i j : ℤ) (U : X.Cᵒᵖ) (x : (M'.complex.X i).val.obj U)
      (y : (N.complex.X j).val.obj U),
      (t.toHomologicalComplex.f (i + j)).val.app U (hT'.tmul i j U x y) =
        hT.tmul i j U ((u.toHomologicalComplex.f i).val.app U x) y)
    (n : ℤ) (φ : HomogeneousMap B T L n) (φ' : HomogeneousMap B T' L n)
    (hφ' : φ'.val = (Cochain.ofHom t.toHomologicalComplex).comp φ.val (zero_add n)) :
    (tensorHomHomogeneousEquiv hT' hH n φ').val =
      (Cochain.ofHom u.toHomologicalComplex).comp
        (tensorHomHomogeneousEquiv hT hH n φ).val (zero_add n) := by
  refine Cochain.ext _ _ fun p q hpq => homSections_ext fun U x => ?_
  obtain ⟨U⟩ := U
  rw [homSections_ofHom_comp_v]
  refine hH.isInternalHom.sections_ext fun j k hjk W y => ?_
  have hnat : (M.complex.X p).val.map W.hom.op
        ((u.toHomologicalComplex.f p).val.app (Opposite.op U) x) =
      (u.toHomologicalComplex.f p).val.app (Opposite.op W.left)
        ((M'.complex.X p).val.map W.hom.op x) :=
    homSections_naturality (u.toHomologicalComplex.f p) W.hom.op x
  rw [homogeneousEquiv_sectionsEquiv_app hT' hH n φ' p q hpq U x j k hjk W y,
    hφ', homSections_ofHom_comp_v t.toHomologicalComplex φ.val (p + j) k (by omega),
    ht p j (Opposite.op W.left) ((M'.complex.X p).val.map W.hom.op x) y,
    homogeneousEquiv_sectionsEquiv_app hT hH n φ p q hpq U
      ((u.toHomologicalComplex.f p).val.app (Opposite.op U) x) j k hjk W y, hnat]

/-- **Tensor-hom adjunction for sheaves of differential graded modules**, first identity,
functoriality in `L`: a morphism `k : L ⟶ L'` of right differential graded `B`-modules induces
`g : SheafHom^dg_B(N, L) ⟶ SheafHom^dg_B(N, L')`, and the identification of the hom-complexes
carries postcomposition with `k` to postcomposition with `g`. -/
@[stacks 0FRS "functoriality of the hom-complex identity in L: a morphism L ⟶ L', with the \
induced map of internal homs, commutes with the identification"]
theorem homogeneousEquiv_naturality_right (hT : IsTensorProduct M N T)
    (hH : IsSheafHom N L H) (hH' : IsSheafHom N L' H') (k : L ⟶ L') (g : H ⟶ H')
    (hg : ∀ (m : ℤ) (U : X.C) (p : (H.complex.X m).val.obj (Opposite.op U)) (i j : ℤ)
      (hij : i + m = j) (V : Over U) (y : (N.complex.X i).val.obj (Opposite.op V.left)),
      (hH'.isInternalHom.sectionsEquiv m U
          ((g.toHomologicalComplex.f m).val.app (Opposite.op U) p)).app i j hij V y =
        (k.toHomologicalComplex.f j).val.app (Opposite.op V.left)
          ((hH.isInternalHom.sectionsEquiv m U p).app i j hij V y))
    (n : ℤ) (φ : HomogeneousMap B T L n) (φ' : HomogeneousMap B T L' n)
    (hφ' : φ'.val = φ.val.comp (Cochain.ofHom k.toHomologicalComplex) (add_zero n)) :
    (tensorHomHomogeneousEquiv hT hH' n φ').val =
      (tensorHomHomogeneousEquiv hT hH n φ).val.comp
        (Cochain.ofHom g.toHomologicalComplex) (add_zero n) := by
  refine Cochain.ext _ _ fun p q hpq => homSections_ext fun U x => ?_
  obtain ⟨U⟩ := U
  rw [homSections_comp_ofHom_v]
  refine hH'.isInternalHom.sections_ext fun j k' hjk W y => ?_
  rw [homogeneousEquiv_sectionsEquiv_app hT hH' n φ' p q hpq U x j k' hjk W y,
    hφ', homSections_comp_ofHom_v φ.val k.toHomologicalComplex (p + j) k' (by omega),
    hg q U _ j k' hjk W y,
    homogeneousEquiv_sectionsEquiv_app hT hH n φ p q hpq U x j k' hjk W y]

/-- **Tensor-hom adjunction for sheaves of differential graded modules**, first identity,
functoriality in `N`: a morphism `σ : N ⟶ N'` of differential graded `(A, B)`-bimodules induces
`t : M ⊗_A N ⟶ M ⊗_A N'` and `g : SheafHom^dg_B(N', L) ⟶ SheafHom^dg_B(N, L)`, and the
identification of the hom-complexes carries precomposition with `t` to postcomposition with
`g`. -/
@[stacks 0FRS "functoriality of the hom-complex identity in N: a morphism N ⟶ N' of bimodules, \
compatible with the tensor products and the internal homs, commutes with the identification"]
theorem homogeneousEquiv_naturality_bimodule (hT : IsTensorProduct M N T)
    (hT' : IsTensorProduct M N' T') (hH : IsSheafHom N L H) (hH' : IsSheafHom N' L H')
    (σ : N ⟶ N') (t : T ⟶ T') (g : H' ⟶ H)
    (ht : ∀ (i j : ℤ) (U : X.Cᵒᵖ) (x : (M.complex.X i).val.obj U)
      (y : (N.complex.X j).val.obj U),
      (t.toHomologicalComplex.f (i + j)).val.app U (hT.tmul i j U x y) =
        hT'.tmul i j U x ((σ.toHomologicalComplex.f j).val.app U y))
    (hg : ∀ (m : ℤ) (U : X.C) (p : (H'.complex.X m).val.obj (Opposite.op U)) (i j : ℤ)
      (hij : i + m = j) (V : Over U) (y : (N.complex.X i).val.obj (Opposite.op V.left)),
      (hH.isInternalHom.sectionsEquiv m U
          ((g.toHomologicalComplex.f m).val.app (Opposite.op U) p)).app i j hij V y =
        (hH'.isInternalHom.sectionsEquiv m U p).app i j hij V
          ((σ.toHomologicalComplex.f i).val.app (Opposite.op V.left) y))
    (n : ℤ) (φ : HomogeneousMap B T L n) (φ' : HomogeneousMap B T' L n)
    (hφ : φ.val = (Cochain.ofHom t.toHomologicalComplex).comp φ'.val (zero_add n)) :
    (tensorHomHomogeneousEquiv hT hH n φ).val =
      (tensorHomHomogeneousEquiv hT' hH' n φ').val.comp
        (Cochain.ofHom g.toHomologicalComplex) (add_zero n) := by
  refine Cochain.ext _ _ fun p q hpq => homSections_ext fun U x => ?_
  obtain ⟨U⟩ := U
  rw [homSections_comp_ofHom_v]
  refine hH.isInternalHom.sections_ext fun j k hjk W y => ?_
  rw [homogeneousEquiv_sectionsEquiv_app hT hH n φ p q hpq U x j k hjk W y,
    hφ, homSections_ofHom_comp_v t.toHomologicalComplex φ'.val (p + j) k (by omega),
    ht p j (Opposite.op W.left) ((M.complex.X p).val.map W.hom.op x) y,
    hg q U _ j k hjk W y,
    homogeneousEquiv_sectionsEquiv_app hT' hH' n φ' p q hpq U x j k hjk W
      ((σ.toHomologicalComplex.f j).val.app (Opposite.op W.left) y)]

end Naturality

end FirstIdentity

end SheafOfModules.DifferentialGradedModule

end
