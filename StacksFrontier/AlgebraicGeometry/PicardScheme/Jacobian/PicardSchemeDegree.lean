module

public import StacksFrontier.AlgebraicGeometry.Picard.RelativeCurveDegreeLocallyConstant
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.PicardRepresentable
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Subgroups.Defs

/-!
# The degree components of a Picard scheme (Stacks 0BA0 (1), (3))

Let `P` be a group scheme over `S` representing the rigidified Picard functor `Pic_{X/S,σ}` of a
flat proper relative curve `X ⟶ S` with a section. The universal class on `X_P` has a degree on
every fibre of `X_P ⟶ P`, which is locally constant by [Stacks, Tag 0B9T]
(`AlgebraicGeometry.isLocallyConstant_relativeInvertibleDegreeHom`). So `P` is the disjoint union
of the open and closed subschemes `P^d` where the universal class has degree `d`, and a morphism
`T ⟶ P` lands in `P^d` exactly when the class it classifies has degree `d` on every fibre of
`X_T ⟶ T`. This is the decomposition `Pic_{X/k} = ∐_d Pic^d_{X/k}` of the proof of
[Stacks, Tag 0BA0].

## Main definitions

* `Stacks.RigidifiedPicard.universalClass` — the class on `X_P` classified by `𝟙 P`.
* `Stacks.RigidifiedPicard.degreeLocus` — the open and closed subscheme `P^d`.

## Main results

* `Stacks.RigidifiedPicard.classOf_hom_app` — the class classified by `a : T ⟶ P` is the
  pullback of the universal class.
* `Stacks.RigidifiedPicard.range_subset_degreeLocus_iff` — `a` lands in `P^d` exactly when its
  class has degree `d` everywhere.
* `Stacks.RigidifiedPicard.isClopen_degreeLocus`, `degreeLocus_disjoint`, `iSup_degreeLocus` —
  the decomposition.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.RigidifiedPicard

variable {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f] [IsProper f]
  [LocallyOfFiniteType f] (hdim : ∀ s : S, topologicalKrullDim ↥(f.fiber s) ≤ 1)
  (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S) (P : Grp (Over S)) (e : yonedaGrp.obj P ≅ functor f σ hσ)

/-- The Picard class of `X_T` of an element of `Pic_{X/S,σ}(T)`. -/
abbrev classOfElt {T : Over S} (x : (functor f σ hσ ⋙ forget GrpCat).obj (op T)) :
    Stacks.Picard.ofScheme (bc f T) :=
  smallEquiv _ ((Multiplicative.toAdd x : group f σ hσ T) : Stacks.Picard.smallOfScheme (bc f T))

/-- **The universal class** on `X_P`: the class classified by `𝟙 P`. -/
def universalClass : Stacks.Picard.ofScheme (bc f P.X) :=
  classOfElt f σ hσ ((e.hom.app (op P.X)).hom (𝟙 P.X))

omit [Flat f] [LocallyOfFinitePresentation f] [IsProper f] [LocallyOfFiniteType f] in
/-- The class classified by a morphism `a : T ⟶ P` is the pullback of the universal class. -/
theorem classOf_hom_app {T : Over S} (a : T ⟶ P.X) :
    classOfElt f σ hσ ((e.hom.app (op T)).hom a) =
      Stacks.Picard.schemePullbackClass (bcMap f a) (universalClass f σ hσ P e) := by
  have hn : (e.hom.app (op T)).hom ((yonedaGrp.obj P).map a.op (𝟙 P.X)) =
      (functor f σ hσ).map a.op ((e.hom.app (op P.X)).hom (𝟙 P.X)) :=
    congrArg (fun φ => GrpCat.Hom.hom φ (𝟙 P.X)) (e.hom.naturality a.op)
  have ha : (yonedaGrp.obj P).map a.op (𝟙 P.X) = a := Category.comp_id a
  rw [ha] at hn
  rw [hn, universalClass]
  exact smallEquiv_smallSchemePullbackClassHom _ _

/-- **The degree function on `P`**: the degree of the universal class on the fibre of
`X_P ⟶ P` over a point. -/
def degreeFunction : P.X.left → ℤ :=
  relativeInvertibleDegreeHom (bcProj f P.X) (topologicalKrullDim_fiber_bcProj_le f hdim P.X)
    (universalClass f σ hσ P e)

/-- The degree function on `P` is locally constant. -/
theorem isLocallyConstant_degreeFunction :
    IsLocallyConstant (degreeFunction f hdim σ hσ P e) :=
  isLocallyConstant_relativeInvertibleDegreeHom (bcProj f P.X) (finitePresentation_bcProj f P.X)
    _ _

/-- **`P^d`**, the open subscheme of `P` where the universal class has degree `d`. -/
def degreeLocus (d : ℤ) : P.X.left.Opens :=
  ⟨degreeFunction f hdim σ hσ P e ⁻¹' {d},
    (isLocallyConstant_degreeFunction f hdim σ hσ P e).isOpen_fiber d⟩

/-- A point lies in `P^d` exactly when the degree function takes the value `d` there. -/
theorem mem_degreeLocus_iff (d : ℤ) (p : P.X.left) :
    p ∈ degreeLocus f hdim σ hσ P e d ↔ degreeFunction f hdim σ hσ P e p = d :=
  Iff.rfl

/-- `P^d` is open and closed in `P`. -/
theorem isClopen_degreeLocus (d : ℤ) : IsClopen (degreeLocus f hdim σ hσ P e d : Set P.X.left) :=
  ⟨(isLocallyConstant_degreeFunction f hdim σ hσ P e).isClosed_fiber d,
    (isLocallyConstant_degreeFunction f hdim σ hσ P e).isOpen_fiber d⟩

/-- For `d ≠ d'`, the loci `P^d` and `P^{d'}` are disjoint. -/
theorem degreeLocus_disjoint {d d' : ℤ} (h : d ≠ d') :
    Disjoint (degreeLocus f hdim σ hσ P e d : Set P.X.left) (degreeLocus f hdim σ hσ P e d') :=
  Set.disjoint_left.2 fun _ h₁ h₂ => h (h₁.symm.trans h₂)

/-- The loci `P^d` cover `P`. -/
theorem iSup_degreeLocus : ⨆ d, degreeLocus f hdim σ hσ P e d = ⊤ := by
  refine top_unique fun p _ => ?_
  rw [TopologicalSpace.Opens.mem_iSup]
  exact ⟨_, rfl⟩

/-- **A morphism `a : T ⟶ P` lands in `P^d` exactly when the class it classifies has degree `d`
on every fibre of `X_T ⟶ T`.** -/
theorem range_subset_degreeLocus_iff {T : Over S} (a : T ⟶ P.X) (d : ℤ) :
    Set.range a.left ⊆ (degreeLocus f hdim σ hσ P e d : Set P.X.left) ↔
      ∀ t : T.left, relativeInvertibleDegreeHomAt (bcProj f T)
        (topologicalKrullDim_fiber_bcProj_le f hdim T) t
          (classOfElt f σ hσ ((e.hom.app (op T)).hom a)) = d := by
  rw [classOf_hom_app]
  have h := fun t => congrFun (relativeInvertibleDegreeHom_schemePullbackClass_of_isPullback
    (bcMap_isPullback_proj f a) (topologicalKrullDim_fiber_bcProj_le f hdim P.X)
    (topologicalKrullDim_fiber_bcProj_le f hdim T) (universalClass f σ hσ P e)) t
  simp only [relativeInvertibleDegreeHom_apply, Function.comp_apply] at h
  simp only [h]
  exact ⟨fun hs t => hs ⟨t, rfl⟩, fun hs _ ⟨t, ht⟩ => ht ▸ hs t⟩

/-- `P^d` as an `S`-scheme. -/
abbrev degreeLocusOver (d : ℤ) : Over S :=
  Over.mk ((degreeLocus f hdim σ hσ P e d).ι ≫ P.X.hom)

/-- The inclusion of `P^d` into `P`, over `S`. -/
abbrev degreeLocusι (d : ℤ) : degreeLocusOver f hdim σ hσ P e d ⟶ P.X :=
  Over.homMk (degreeLocus f hdim σ hσ P e d).ι rfl

/-- The inclusion of `Pic⁰_{X/S,σ}` into `Pic_{X/S,σ}`, on elements. -/
def zeroToFull {T : Over S} (x : (functorZero f hdim σ hσ ⋙ forget GrpCat).obj (op T)) :
    (functor f σ hσ ⋙ forget GrpCat).obj (op T) :=
  Multiplicative.ofAdd ((Multiplicative.toAdd x : groupZero f hdim σ hσ T) : group f σ hσ T)

omit [Flat f] [LocallyOfFinitePresentation f] in
/-- The class of an element of `Pic⁰_{X/S,σ}(T)` viewed in `Pic_{X/S,σ}(T)` is its underlying
Picard class. -/
theorem classOfElt_zeroToFull {T : Over S}
    (x : (functorZero f hdim σ hσ ⋙ forget GrpCat).obj (op T)) :
    classOfElt f σ hσ (zeroToFull f hdim σ hσ x) =
      smallEquiv _ ((((Multiplicative.toAdd x : groupZero f hdim σ hσ T) : group f σ hσ T)) :
        Stacks.Picard.smallOfScheme (bc f T)) :=
  rfl

/-- The morphism to `P` classifying an element of `Pic_{X/S,σ}(T)`. -/
def eltHom {T : Over S} (y : (functor f σ hσ ⋙ forget GrpCat).obj (op T)) : T ⟶ P.X :=
  (e.inv.app (op T)).hom y

omit [Flat f] [LocallyOfFinitePresentation f] [IsProper f] [LocallyOfFiniteType f] in
/-- The element classified by the morphism `eltHom y` is `y`. -/
theorem hom_app_inv_app {T : Over S} (y : (functor f σ hσ ⋙ forget GrpCat).obj (op T)) :
    (e.hom.app (op T)).hom (eltHom f σ hσ P e y) = y := by
  change ((e.inv ≫ e.hom).app (op T)).hom y = y
  rw [e.inv_hom_id]
  rfl

omit [Flat f] [LocallyOfFinitePresentation f] [IsProper f] [LocallyOfFiniteType f] in
/-- The morphism classifying the element given by `a : T ⟶ P` is `a`. -/
theorem inv_app_hom_app {T : Over S} (a : T ⟶ P.X) :
    eltHom f σ hσ P e ((e.hom.app (op T)).hom a) = a := by
  change ((e.hom ≫ e.inv).app (op T)).hom a = a
  rw [e.hom_inv_id]
  rfl

omit [Flat f] [LocallyOfFinitePresentation f] [IsProper f] [LocallyOfFiniteType f] in
/-- The element classified by `b ≫ a` is the pullback along `b` of the element classified
by `a`. -/
theorem hom_app_comp {T T' : Over S} (b : T' ⟶ T) (a : T ⟶ P.X) :
    (e.hom.app (op T')).hom (b ≫ a) = (functor f σ hσ).map b.op ((e.hom.app (op T)).hom a) :=
  congrArg (fun φ => GrpCat.Hom.hom φ a) (e.hom.naturality b.op)

/-- The morphism to `P` classifying an element of `Pic⁰_{X/S,σ}(T)` lands in `P⁰`. -/
theorem range_inv_app_subset {T : Over S}
    (x : (functorZero f hdim σ hσ ⋙ forget GrpCat).obj (op T)) :
    Set.range (eltHom f σ hσ P e (zeroToFull f hdim σ hσ x)).left ⊆
      Set.range (degreeLocus f hdim σ hσ P e 0).ι.base := by
  rw [Scheme.Opens.range_ι, range_subset_degreeLocus_iff, hom_app_inv_app, classOfElt_zeroToFull]
  intro t
  have h := (mem_groupZero_iff f hdim σ hσ T _).1 (Multiplicative.toAdd x).2 t
  rwa [degree_apply] at h

/-- The element of `Pic_{X/S,σ}(T)` classified by a morphism `T ⟶ P`. -/
def homElt {T : Over S} (a : T ⟶ P.X) : (functor f σ hσ ⋙ forget GrpCat).obj (op T) :=
  (e.hom.app (op T)).hom a

omit [Flat f] [LocallyOfFinitePresentation f] [IsProper f] [LocallyOfFiniteType f] in
/-- `homElt` is a left inverse of `eltHom`. -/
theorem homElt_eltHom {T : Over S} (y : (functor f σ hσ ⋙ forget GrpCat).obj (op T)) :
    homElt f σ hσ P e (eltHom f σ hσ P e y) = y :=
  hom_app_inv_app f σ hσ P e y

omit [Flat f] [LocallyOfFinitePresentation f] [IsProper f] [LocallyOfFiniteType f] in
/-- A morphism `T ⟶ P` is determined by the element of `Pic_{X/S,σ}(T)` it classifies. -/
theorem homElt_injective {T : Over S} : Function.Injective (homElt f σ hσ P e (T := T)) :=
  fun a a' h => by
    rw [← inv_app_hom_app f σ hσ P e a, ← inv_app_hom_app f σ hσ P e a']
    exact congrArg (eltHom f σ hσ P e) h

omit [Flat f] [LocallyOfFinitePresentation f] [IsProper f] [LocallyOfFiniteType f] in
/-- `homElt` is natural in `T`. -/
theorem homElt_comp {T T' : Over S} (b : T' ⟶ T) (a : T ⟶ P.X) :
    homElt f σ hσ P e (b ≫ a) = (functor f σ hσ ⋙ forget GrpCat).map b.op (homElt f σ hσ P e a) :=
  hom_app_comp f σ hσ P e b a

/-- A morphism to `P` whose range lies in an open `U` factors through `U`, over `S`. -/
private theorem exists_lift_opens {T : Over S} (U : P.X.left.Opens) (b : T ⟶ P.X)
    (hb : Set.range b.left ⊆ Set.range U.ι.base) :
    ∃ a : T ⟶ Over.mk (U.ι ≫ P.X.hom), a ≫ Over.homMk U.ι rfl = b :=
  ⟨Over.homMk (IsOpenImmersion.lift U.ι b.left hb) (by
      change IsOpenImmersion.lift _ _ _ ≫ U.ι ≫ P.X.hom = T.hom
      rw [IsOpenImmersion.lift_fac_assoc, Over.w b]),
    Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)⟩

/-- The element classified by a morphism `T ⟶ P` factoring through `P⁰` lies in
`Pic⁰_{X/S,σ}(T)`. -/
theorem homElt_degreeLocusι_mem {T : Over S} (a : T ⟶ degreeLocusOver f hdim σ hσ P e 0) :
    (Multiplicative.toAdd (homElt f σ hσ P e (a ≫ degreeLocusι f hdim σ hσ P e 0)) :
      group f σ hσ T) ∈ groupZero f hdim σ hσ T :=
  (mem_groupZero_iff f hdim σ hσ T _).2 fun t =>
    (range_subset_degreeLocus_iff f hdim σ hσ P e (a ≫ degreeLocusι f hdim σ hσ P e 0) 0).1 (by
      rintro _ ⟨x, rfl⟩
      rw [← Scheme.Opens.range_ι]
      exact ⟨a.left x, rfl⟩) t

/-- The element of `Pic⁰_{X/S,σ}(T)` classified by a morphism `T ⟶ P⁰`. -/
def toZero {T : Over S} (a : T ⟶ degreeLocusOver f hdim σ hσ P e 0) :
    (functorZero f hdim σ hσ ⋙ forget GrpCat).obj (op T) :=
  Multiplicative.ofAdd ⟨_, homElt_degreeLocusι_mem f hdim σ hσ P e a⟩

/-- Morphisms `T ⟶ P⁰` correspond bijectively to elements of `Pic⁰_{X/S,σ}(T)`. -/
theorem toZero_bijective {T : Over S} : Function.Bijective (toZero f hdim σ hσ P e (T := T)) := by
  refine ⟨fun a a' h => ?_, fun x => ?_⟩
  · have h' : homElt f σ hσ P e (a ≫ degreeLocusι f hdim σ hσ P e 0) =
        homElt f σ hσ P e (a' ≫ degreeLocusι f hdim σ hσ P e 0) :=
      congrArg (zeroToFull f hdim σ hσ) h
    exact Over.OverMorphism.ext ((cancel_mono (degreeLocus f hdim σ hσ P e 0).ι).1
      (congrArg CommaMorphism.left (homElt_injective f σ hσ P e h')))
  · let b : T ⟶ P.X := eltHom f σ hσ P e (zeroToFull f hdim σ hσ x)
    have hb : Set.range b.left ⊆ Set.range (degreeLocus f hdim σ hσ P e 0).ι.base :=
      range_inv_app_subset f hdim σ hσ P e x
    obtain ⟨a, ha⟩ := exists_lift_opens P _ b hb
    refine ⟨a, ?_⟩
    change Multiplicative.ofAdd ⟨Multiplicative.toAdd (homElt f σ hσ P e
      (a ≫ degreeLocusι f hdim σ hσ P e 0)), _⟩ = x
    simp only [ha, b, homElt_eltHom]
    rfl

/-- **`P⁰` represents `Pic⁰_{X/S,σ}`.** -/
def degreeLocusZeroRepresentableBy :
    (functorZero f hdim σ hσ ⋙ forget GrpCat).RepresentableBy
      (degreeLocusOver f hdim σ hσ P e 0) where
  homEquiv := Equiv.ofBijective _ (toZero_bijective f hdim σ hσ P e)
  homEquiv_comp {T T'} b a := by
    change toZero f hdim σ hσ P e (b ≫ a) =
      (functorZero f hdim σ hσ ⋙ forget GrpCat).map b.op (toZero f hdim σ hσ P e a)
    refine congrArg Multiplicative.ofAdd (Subtype.ext ?_)
    change (Multiplicative.toAdd (homElt f σ hσ P e ((b ≫ a) ≫ degreeLocusι f hdim σ hσ P e 0)) :
      group f σ hσ T) = groupMap f σ hσ b
        (Multiplicative.toAdd (homElt f σ hσ P e (a ≫ degreeLocusι f hdim σ hσ P e 0)))
    rw [Category.assoc, homElt_comp]
    rfl

/-! ### `P⁰` is a subgroup scheme -/

/-- A morphism to `P` whose class has degree `d` on every fibre factors through `P^d`. -/
theorem exists_lift_degreeLocus {T : Over S} (a : T ⟶ P.X) (d : ℤ)
    (ha : ∀ t : T.left, relativeInvertibleDegreeHomAt (bcProj f T)
      (topologicalKrullDim_fiber_bcProj_le f hdim T) t
        (classOfElt f σ hσ ((e.hom.app (op T)).hom a)) = d) :
    ∃ a' : T ⟶ degreeLocusOver f hdim σ hσ P e d, a' ≫ degreeLocusι f hdim σ hσ P e d = a := by
  have hr := (range_subset_degreeLocus_iff f hdim σ hσ P e a d).2 ha
  exact exists_lift_opens P _ a (by rwa [Scheme.Opens.range_ι])

omit [Flat f] [LocallyOfFinitePresentation f] [IsProper f] [LocallyOfFiniteType f] in
/-- The class of a product is the sum of the classes. -/
theorem classOfElt_mul {T : Over S} (x y : (functor f σ hσ ⋙ forget GrpCat).obj (op T)) :
    classOfElt f σ hσ (x * y) = classOfElt f σ hσ x + classOfElt f σ hσ y :=
  map_add (smallEquiv (bc f T)) _ _

omit [Flat f] [LocallyOfFinitePresentation f] [IsProper f] [LocallyOfFiniteType f] in
/-- The class of an inverse is the negative of the class. -/
theorem classOfElt_inv {T : Over S} (x : (functor f σ hσ ⋙ forget GrpCat).obj (op T)) :
    classOfElt f σ hσ x⁻¹ = -classOfElt f σ hσ x :=
  map_neg (smallEquiv (bc f T)) _

omit [Flat f] [LocallyOfFinitePresentation f] [IsProper f] [LocallyOfFiniteType f] in
/-- The class of the identity element is zero. -/
theorem classOfElt_one {T : Over S} :
    classOfElt f σ hσ (1 : (functor f σ hσ ⋙ forget GrpCat).obj (op T)) = 0 :=
  map_zero (smallEquiv (bc f T))

omit [Flat f] [LocallyOfFinitePresentation f] [IsProper f] [LocallyOfFiniteType f] in
/-- `homElt` sends the product of morphisms `T ⟶ P` to the product of elements. -/
theorem homElt_mul {T : Over S} (a b : T ⟶ P.X) :
    homElt f σ hσ P e (a * b) = homElt f σ hσ P e a * homElt f σ hσ P e b :=
  (e.hom.app (op T)).hom.map_mul a b

omit [Flat f] [LocallyOfFinitePresentation f] [IsProper f] [LocallyOfFiniteType f] in
/-- `homElt` sends the identity morphism `T ⟶ P` to the identity element. -/
theorem homElt_one {T : Over S} : homElt f σ hσ P e (1 : T ⟶ P.X) = 1 :=
  (e.hom.app (op T)).hom.map_one

omit [Flat f] [LocallyOfFinitePresentation f] [IsProper f] [LocallyOfFiniteType f] in
/-- `homElt` sends the inverse of a morphism `T ⟶ P` to the inverse element. -/
theorem homElt_inv {T : Over S} (a : T ⟶ P.X) :
    homElt f σ hσ P e a⁻¹ = (homElt f σ hσ P e a)⁻¹ :=
  (e.hom.app (op T)).hom.map_inv a

/-- **[Stacks, Tag 0BA0] (3): `P⁰` is an open (and closed) subgroup scheme of `P`.** -/
theorem exists_openSubgroupScheme_degreeLocus_zero :
    ∃ K : OpenSubgroupScheme P, ∃ i : degreeLocusOver f hdim σ hσ P e 0 ≅ K.carrier.X,
      degreeLocusι f hdim σ hσ P e 0 = i.hom ≫ K.ι.hom.hom := by
  have : IsOpenImmersion (degreeLocusι f hdim σ hσ P e 0).left :=
    inferInstanceAs (IsOpenImmersion (degreeLocus f hdim σ hσ P e 0).ι)
  rw [isOpenSubgroupScheme_iff_factor]
  have hdeg0 : ∀ {T : Over S} (a : T ⟶ degreeLocusOver f hdim σ hσ P e 0) (t : T.left),
      relativeInvertibleDegreeHomAt (bcProj f T) (topologicalKrullDim_fiber_bcProj_le f hdim T) t
        (classOfElt f σ hσ (homElt f σ hσ P e (a ≫ degreeLocusι f hdim σ hσ P e 0))) = 0 :=
    fun a t => (mem_groupZero_iff f hdim σ hσ _ _).1 (homElt_degreeLocusι_mem f hdim σ hσ P e a) t
  refine ⟨?_, ?_, ?_⟩
  · refine exists_lift_degreeLocus f hdim σ hσ P e _ 0 fun t => ?_
    change relativeInvertibleDegreeHomAt _ _ t (classOfElt f σ hσ (homElt f σ hσ P e η[P.X])) = 0
    rw [show (η[P.X] : 𝟙_ (Over S) ⟶ P.X) = 1 by rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _),
      Category.id_comp], homElt_one, classOfElt_one, map_zero]
  · refine exists_lift_degreeLocus f hdim σ hσ P e _ 0 fun t => ?_
    have hmul : (degreeLocusι f hdim σ hσ P e 0 ⊗ₘ degreeLocusι f hdim σ hσ P e 0) ≫ μ[P.X] =
        (fst _ _ ≫ degreeLocusι f hdim σ hσ P e 0) *
          (snd _ _ ≫ degreeLocusι f hdim σ hσ P e 0) := by
      simp [Hom.mul_def]
    change relativeInvertibleDegreeHomAt _ _ t (classOfElt f σ hσ (homElt f σ hσ P e
      ((degreeLocusι f hdim σ hσ P e 0 ⊗ₘ degreeLocusι f hdim σ hσ P e 0) ≫ μ[P.X]))) = 0
    rw [hmul, homElt_mul, classOfElt_mul, map_add, hdeg0, hdeg0, add_zero]
  · refine exists_lift_degreeLocus f hdim σ hσ P e _ 0 fun t => ?_
    have hinv : degreeLocusι f hdim σ hσ P e 0 ≫ ι[P.X] = (degreeLocusι f hdim σ hσ P e 0)⁻¹ :=
      (Hom.inv_def _).symm
    change relativeInvertibleDegreeHomAt _ _ t (classOfElt f σ hσ (homElt f σ hσ P e
      (degreeLocusι f hdim σ hσ P e 0 ≫ ι[P.X]))) = 0
    rw [hinv, homElt_inv, classOfElt_inv, map_neg]
    have := hdeg0 (𝟙 _) t
    rw [Category.id_comp] at this
    rw [this, neg_zero]

end Stacks.RigidifiedPicard

end
