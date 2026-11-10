module

public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.ConormalTwistedFractionClass

/-!
# Complexes on an open subscheme read on the ambient scheme

Let `X` be a scheme, `W ⊆ X` an open subscheme with inclusion `ι : W ⟶ X`, `ℱ` an
`𝒪_X`-module and `K^•` a complex of `𝒪_W`-modules, indexed by `ℕ`, whose degree-`0` term is
`ℱ|_W`.  The *splice* of `K^•` is the complex of `𝒪_X`-modules

`ℱ ⟶ ι_* K¹ ⟶ ι_* K² ⟶ ⋯`

whose first differential is the unit `ℱ ⟶ ι_*(ℱ|_W)` followed by `ι_*` of the first differential
of `K^•`.  Its restriction to `W` is `K^•` again, and its degree-`0` term is `ℱ` itself, so it
carries the projection onto `ℱ` placed in degree `0`.

## Main definitions

* `Stacks.Perfect.ConormalClass.splice`: the splice of a complex on `W`.
* `Stacks.Perfect.ConormalClass.spliceMap`: the map of splices induced by a map of complexes.
* `Stacks.Perfect.ConormalClass.restrictSpliceIso`: the restriction of the splice to `W` is the
  complex it was built from.

## Main results

* `Stacks.Perfect.ConormalClass.restrictSpliceIso_hom_f_zero`: the restriction isomorphism is
  the given identification in degree `0`.
* `Stacks.Perfect.ConormalClass.cohomologySupportedOn_splice`: the splice is supported where the
  complex it was built from is.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.Perfect.ConormalClass

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : Scheme.{u}} (W : X.Opens)

/-- The direct image along the inclusion of an open subscheme. -/
abbrev push : W.toScheme.Modules ⥤ X.Modules := Scheme.Modules.pushforward W.ι

/-- The restriction to an open subscheme. -/
abbrev res : X.Modules ⥤ W.toScheme.Modules := Scheme.Modules.restrictFunctor W.ι

/-- The unit `ℱ ⟶ ι_*(ℱ|_W)` of the restriction adjunction. -/
abbrev unitW (F : X.Modules) : F ⟶ (push W).obj ((res W).obj F) :=
  (Scheme.Modules.restrictAdjunction W.ι).unit.app F

/-- The counit `(ι_* M)|_W ⟶ M` of the restriction adjunction, an isomorphism. -/
abbrev counitW (M : W.toScheme.Modules) : (res W).obj ((push W).obj M) ⟶ M :=
  (Scheme.Modules.restrictAdjunction W.ι).counit.app M

/-- The counit of the restriction adjunction as an isomorphism. -/
def counitWIso (M : W.toScheme.Modules) : (res W).obj ((push W).obj M) ≅ M :=
  (asIso (Scheme.Modules.restrictAdjunction W.ι).counit).app M

/-- The forward map of `counitWIso` is the counit. -/
@[simp] theorem counitWIso_hom (M : W.toScheme.Modules) : (counitWIso W M).hom = counitW W M :=
  rfl

/-- The left triangle identity of the restriction adjunction. -/
@[reassoc (attr := simp)]
theorem res_map_unitW_comp_counitW (F : X.Modules) :
    (res W).map (unitW W F) ≫ counitW W ((res W).obj F) = 𝟙 _ :=
  (Scheme.Modules.restrictAdjunction W.ι).left_triangle_components F

/-- Naturality of the counit of the restriction adjunction. -/
@[reassoc]
theorem res_map_push_map_comp_counitW {M N : W.toScheme.Modules} (g : M ⟶ N) :
    (res W).map ((push W).map g) ≫ counitW W N = counitW W M ≫ g :=
  (Scheme.Modules.restrictAdjunction W.ι).counit.naturality g

section Splice

variable (F : X.Modules) (K : CochainComplex W.toScheme.Modules ℕ) (e : K.X 0 ≅ (res W).obj F)

/-- The terms of the splice: `ℱ` in degree `0` and the direct images of the terms of `K^•` in
positive degrees. -/
abbrev spliceX : ℕ → X.Modules
  | 0 => F
  | n + 1 => (push W).obj (K.X (n + 1))

/-- The differentials of the splice. -/
def spliceD : ∀ n : ℕ, spliceX W F K n ⟶ spliceX W F K (n + 1)
  | 0 => unitW W F ≫ (push W).map (e.inv ≫ K.d 0 1)
  | n + 1 => (push W).map (K.d (n + 1) (n + 1 + 1))

/-- Consecutive differentials of the splice compose to zero. -/
theorem spliceD_comp_spliceD : ∀ n : ℕ, spliceD W F K e n ≫ spliceD W F K e (n + 1) = 0
  | 0 => by
    change unitW W F ≫ (push W).map (e.inv ≫ K.d 0 1) ≫ (push W).map (K.d 1 2) = 0
    rw [← Functor.map_comp, Category.assoc, K.d_comp_d, comp_zero, Functor.map_zero, comp_zero]
  | n + 1 => by
    change (push W).map (K.d (n + 1) (n + 1 + 1)) ≫
      (push W).map (K.d (n + 1 + 1) (n + 1 + 1 + 1)) = 0
    rw [← Functor.map_comp, K.d_comp_d, Functor.map_zero]

/-- **The splice** `ℱ ⟶ ι_* K¹ ⟶ ι_* K² ⟶ ⋯` of a complex on the open subscheme `W` whose
degree-`0` term is `ℱ|_W`. -/
def splice : CochainComplex X.Modules ℕ :=
  CochainComplex.of (spliceX W F K) (spliceD W F K e) (spliceD_comp_spliceD W F K e)

/-- The degree-`0` term of the splice is `ℱ`. -/
theorem splice_X_zero : (splice W F K e).X 0 = F := rfl

/-- The degree-`(n + 1)` term of the splice is `ι_* Kⁿ⁺¹`. -/
theorem splice_X_succ (n : ℕ) : (splice W F K e).X (n + 1) = (push W).obj (K.X (n + 1)) := rfl

/-- The first differential of the splice is the unit `ℱ ⟶ ι_*(ℱ|_W)` followed by `ι_*` of the
first differential of `K^•`. -/
theorem splice_d_zero :
    (splice W F K e).d 0 1 = unitW W F ≫ (push W).map (e.inv ≫ K.d 0 1) :=
  CochainComplex.of_d (spliceX W F K) (spliceD W F K e) 0

/-- In positive degrees the differential of the splice is `ι_*` of the differential of `K^•`. -/
theorem splice_d_succ (n : ℕ) :
    (splice W F K e).d (n + 1) (n + 1 + 1) = (push W).map (K.d (n + 1) (n + 1 + 1)) :=
  CochainComplex.of_d (spliceX W F K) (spliceD W F K e) (n + 1)

/-- The restriction of the first differential of the splice, followed by the counit, is the first
differential of `K^•` after the identification of degree `0`. -/
theorem res_map_spliceD_zero_comp_counitW :
    (res W).map (unitW W F ≫ (push W).map (e.inv ≫ K.d 0 1)) ≫ counitW W (K.X 1) =
      e.inv ≫ K.d 0 1 := by
  rw [Functor.map_comp, Category.assoc, res_map_push_map_comp_counitW,
    res_map_unitW_comp_counitW_assoc]

/-- The components of the restriction isomorphism. -/
def restrictSpliceIsoX : ∀ n : ℕ,
    (((res W).mapHomologicalComplex (ComplexShape.up ℕ)).obj (splice W F K e)).X n ≅ K.X n
  | 0 => e.symm
  | n + 1 => counitWIso W (K.X (n + 1))

/-- **The restriction of the splice to `W` is the complex it was built from.** -/
def restrictSpliceIso :
    ((res W).mapHomologicalComplex (ComplexShape.up ℕ)).obj (splice W F K e) ≅ K :=
  HomologicalComplex.Hom.isoOfComponents (restrictSpliceIsoX W F K e) (by
    rintro i j (rfl : i + 1 = j)
    cases i with
    | zero =>
      change e.inv ≫ K.d 0 1 = (res W).map ((splice W F K e).d 0 1) ≫ counitW W (K.X 1)
      rw [splice_d_zero]
      exact (res_map_spliceD_zero_comp_counitW W F K e).symm
    | succ n =>
      change counitW W (K.X (n + 1)) ≫ K.d (n + 1) (n + 1 + 1) =
        (res W).map ((splice W F K e).d (n + 1) (n + 1 + 1)) ≫ counitW W (K.X (n + 1 + 1))
      refine Eq.trans ?_ (congrArg (fun φ => (res W).map φ ≫ counitW W (K.X (n + 1 + 1)))
        (splice_d_succ W F K e n)).symm
      exact (res_map_push_map_comp_counitW W _).symm)

/-- In degree `0` the restriction isomorphism is the inverse of the identification `e`. -/
theorem restrictSpliceIso_hom_f_zero : (restrictSpliceIso W F K e).hom.f 0 = e.inv := rfl

/-- In positive degrees the restriction isomorphism is the counit. -/
theorem restrictSpliceIso_hom_f_succ (n : ℕ) :
    (restrictSpliceIso W F K e).hom.f (n + 1) = counitW W (K.X (n + 1)) := rfl

end Splice


/-! ### Functoriality of the splice -/

section Map

variable {F G : X.Modules} (φ₀ : F ⟶ G) {K K' : CochainComplex W.toScheme.Modules ℕ}
  (e : K.X 0 ≅ (res W).obj F) (e' : K'.X 0 ≅ (res W).obj G) (φ : K ⟶ K')
  (hφ : φ.f 0 ≫ e'.hom = e.hom ≫ (res W).map φ₀)

/-- The components of the map of splices induced by a map of complexes. -/
def spliceMapF : ∀ n : ℕ, (splice W F K e).X n ⟶ (splice W G K' e').X n
  | 0 => φ₀
  | n + 1 => (push W).map (φ.f (n + 1))

include hφ in
/-- The components of `spliceMapF` in degrees `0` and `1` commute with the first differentials
of the splices. -/
theorem spliceMap_comm_zero :
    φ₀ ≫ unitW W G ≫ (push W).map (e'.inv ≫ K'.d 0 1) =
      (unitW W F ≫ (push W).map (e.inv ≫ K.d 0 1)) ≫ (push W).map (φ.f 1) := by
  have h0 : (res W).map φ₀ ≫ e'.inv = e.inv ≫ φ.f 0 := by
    rw [Iso.eq_inv_comp, ← Category.assoc, ← hφ, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have hu : φ₀ ≫ unitW W G = unitW W F ≫ (push W).map ((res W).map φ₀) :=
    ((Scheme.Modules.restrictAdjunction W.ι).unit.naturality φ₀)
  rw [← Category.assoc, hu, Category.assoc, Category.assoc, ← Functor.map_comp,
    ← Functor.map_comp, ← Category.assoc, h0, Category.assoc, Category.assoc, ← φ.comm]

/-- The components of `spliceMapF` in positive degrees commute with the differentials of the
splices. -/
theorem spliceMap_comm_succ (n : ℕ) :
    (push W).map (φ.f (n + 1)) ≫ (push W).map (K'.d (n + 1) (n + 1 + 1)) =
      (push W).map (K.d (n + 1) (n + 1 + 1)) ≫ (push W).map (φ.f (n + 1 + 1)) := by
  rw [← Functor.map_comp, ← Functor.map_comp, φ.comm]

include hφ in
/-- **The map of splices induced by a map of coefficient modules and a compatible map of
complexes.** -/
def spliceMap : splice W F K e ⟶ splice W G K' e' :=
  CochainComplex.ofHom (spliceMapF W φ₀ e e' φ) (by
    intro n
    cases n with
    | zero =>
      exact (congrArg (fun g => φ₀ ≫ g) (splice_d_zero W G K' e')).trans
        ((spliceMap_comm_zero W φ₀ e e' φ hφ).trans
          (congrArg (fun g => g ≫ (push W).map (φ.f 1)) (splice_d_zero W F K e).symm))
    | succ n =>
      exact (congrArg (fun g => (push W).map (φ.f (n + 1)) ≫ g) (splice_d_succ W G K' e' n)).trans
        ((spliceMap_comm_succ W φ n).trans
          (congrArg (fun g => g ≫ (push W).map (φ.f (n + 1 + 1))) (splice_d_succ W F K e n).symm)))

/-- In degree `0` the map of splices is `φ₀`. -/
theorem spliceMap_f_zero : (spliceMap W φ₀ e e' φ hφ).f 0 = φ₀ := rfl

/-- In degree `n + 1` the map of splices is `ι_*` of the component of `φ`. -/
theorem spliceMap_f_succ (n : ℕ) :
    (spliceMap W φ₀ e e' φ hφ).f (n + 1) = (push W).map (φ.f (n + 1)) := rfl

end Map

/-! ### Stalks of the cohomology of an extended complex -/

section Stalks

variable {Y : Scheme.{u}}

/-- The stalk of the underlying abelian presheaf of a module, as a functor. -/
abbrev stalkF (y : Y) : Y.Modules ⥤ Ab.{u} :=
  Scheme.Modules.toPresheaf Y ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} y

/-- The derived cohomology of an `ℕ`-indexed complex, extended to `ℤ`, is its cohomology in
nonnegative degrees. -/
def derivedHomologyExtendIso (L : CochainComplex Y.Modules ℕ) (n : ℕ) :
    (DerivedCategory.homologyFunctor Y.Modules (n : ℤ)).obj
        (DerivedCategory.Q.obj (L.extend ComplexShape.embeddingUpNat)) ≅ L.homology n :=
  (DerivedCategory.homologyFunctorFactors Y.Modules (n : ℤ)).app _ ≪≫
    L.extendHomologyIso ComplexShape.embeddingUpNat (rfl : ComplexShape.embeddingUpNat.f n = n)

/-- The derived cohomology of an extended complex vanishes in negative degrees. -/
theorem isZero_derivedHomology_extend_of_neg (L : CochainComplex Y.Modules ℕ) (i : ℤ)
    (hi : ∀ n : ℕ, (n : ℤ) ≠ i) :
    IsZero ((DerivedCategory.homologyFunctor Y.Modules i).obj
        (DerivedCategory.Q.obj (L.extend ComplexShape.embeddingUpNat))) := by
  refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctorFactors Y.Modules i).app _)
  exact ((L.extend ComplexShape.embeddingUpNat).exactAt_iff_isZero_homology i).1
    (L.extend_exactAt ComplexShape.embeddingUpNat i hi)

/-- The stalks of the derived cohomology of an extended complex vanish at a point as soon as
the stalks of its cohomology do. -/
theorem isZero_stalk_derivedHomology_extend (L : CochainComplex Y.Modules ℕ) (y : Y)
    (h : ∀ n : ℕ, IsZero ((stalkF y).obj (L.homology n))) (i : ℤ) :
    IsZero ((stalkF y).obj ((DerivedCategory.homologyFunctor Y.Modules i).obj
        (DerivedCategory.Q.obj (L.extend ComplexShape.embeddingUpNat)))) := by
  by_cases hi : ∃ n : ℕ, (n : ℤ) = i
  · obtain ⟨n, rfl⟩ := hi
    exact (h n).of_iso ((stalkF y).mapIso (derivedHomologyExtendIso L n))
  · exact Functor.map_isZero _ (isZero_derivedHomology_extend_of_neg L i fun n hn => hi ⟨n, hn⟩)

end Stalks

/-! ### The support of the splice -/

section Support

variable {W} (F : X.Modules) (K : CochainComplex W.toScheme.Modules ℕ) (e : K.X 0 ≅ (res W).obj F)

/-- The stalk at a point of `W` of the cohomology of the splice is the stalk of the cohomology
of the complex it was built from. -/
def stalkSpliceHomologyIso (y : W.toScheme) (n : ℕ) :
    (stalkF (W.ι y)).obj ((splice W F K e).homology n) ≅ (stalkF y).obj (K.homology n) :=
  ((Scheme.Modules.restrictStalkNatIso W.ι y).app _).symm ≪≫
    (stalkF y).mapIso
      ((Stacks.Perfect.CechSupportRepresentation.mapHomologyIso (res W) (splice W F K e) n).symm ≪≫
        (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) n).mapIso
          (restrictSpliceIso W F K e))

/-- **The splice is supported where the complex it was built from is.**  If the cohomology
sheaves of `K^•` are supported on `T' ⊆ W` and every point of `X` outside `T` lies in `W`
outside `T'`, then the cohomology sheaves of the splice are supported on `T`. -/
theorem cohomologySupportedOn_splice {T' : Set W.toScheme} {T : Set X}
    (hK : AlgebraicGeometry.CohomologySupportedOn (structureSheafRing W.toScheme.toRingedSpace) T'
      (DerivedCategory.Q.obj (K.extend ComplexShape.embeddingUpNat)))
    (hT : ∀ x : X, x ∉ T → ∃ y : W.toScheme, W.ι y = x ∧ y ∉ T') :
    AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X.toRingedSpace) T
      (DerivedCategory.Q.obj ((splice W F K e).extend ComplexShape.embeddingUpNat)) := by
  intro i x hx
  obtain ⟨y, rfl, hy⟩ := hT x hx
  refine isZero_stalk_derivedHomology_extend (splice W F K e) (W.ι y) (fun n => ?_) i
  refine IsZero.of_iso ?_ (stalkSpliceHomologyIso F K e y n)
  exact (hK n y hy).of_iso ((stalkF y).mapIso (derivedHomologyExtendIso K n)).symm

end Support

end Stacks.Perfect.ConormalClass
