module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Topology.Sheaves.LocallySurjective
public import StacksFrontier.AlgebraicGeometry.Morphisms.ImmersionsAndAffine.ClosedImmersionIdealSheaves
public import StacksCore.Tactic.StacksAttribute

/-!
# The exact sequence for a union of two closed subschemes

For two closed subschemes of a scheme, the structure sheaves of their
scheme-theoretic union and intersection fit into the usual short exact sequence.

## Main definitions

* `closedSubschemeStructureSheaf` is the structure sheaf of a closed subscheme, pushed
  forward and regarded as a module on the ambient scheme.
* `ambientToPushforward` is the comparison map from the structure sheaf of the target of a
  morphism of schemes to the direct image of the structure sheaf of its source, and
  `ambientToClosedSubscheme` is its value at the closed immersion of a closed subscheme.
* `closedSubschemeRestriction` is the canonical map between such modules induced by an
  inclusion of closed subschemes.
* `unionToBiprod` and `biprodToIntersection` are the two canonical maps in the sequence.
* `closedSubschemeStructureSheafBotIso` identifies the structure sheaf of the closed subscheme
  cut out by `⊥` with the ambient structure sheaf.

## Main results

* `unionIntersection_shortExact` states that the canonical sequence associated to two
  closed subschemes is short exact.
* `closedSubschemeRestriction_app_top` identifies `closedSubschemeRestriction` on sections over
  the whole space with the map on global functions of the inclusion of the closed subschemes.
* `epi_ambientToPushforward` states that the comparison map of a closed immersion is an
  epimorphism, and `epi_pushforward_map_biprodToIntersection` that the second arrow of the
  sequence stays an epimorphism after a direct image along a morphism that carries the
  scheme-theoretic intersection to a closed subscheme of the target.

## Implementation notes

A closed subscheme is represented by `Scheme.IdealSheafData`. For ideal sheaves `I` and
`J`, their scheme-theoretic union is cut out by `I ⊓ J`, while their scheme-theoretic
intersection is cut out by `I ⊔ J`. The middle object is a biproduct, which is also the
finite product in the abelian category of modules. The second arrow uses the first canonical
map minus the second one.

Everything is deduced from `ambientToClosedSubscheme`. On sections over an open set it is
the structure-sheaf map of the closed immersion, so over an affine open it is surjective
with kernel the defining ideal; it is therefore an epimorphism, and the canonical maps
between the pushed-forward structure sheaves are determined by composing with it. Exactness
then becomes a statement about defining ideals: `(I ⊓ J).ideal` is the intersection of the
two ideals and `(I ⊔ J).ideal` is their sum.

The composites appearing in `closedSubschemeRestriction` are compared on sections rather
than as morphisms: the two sides are definitionally equal, but checking that directly forces
the subscheme to be unfolded into the gluing colimit that defines it, whereas the chain of
section-level identities used here is a composite of statements about variables.

## References

* [Stacks Project, Tag 0C4J](https://stacks.math.columbia.edu/tag/0C4J)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- The structure sheaf of the closed subscheme cut out by `I`, pushed forward along its
closed immersion and viewed as a module on the ambient scheme. -/
noncomputable abbrev closedSubschemeStructureSheaf
    {S : Scheme.{u}} (I : S.IdealSheafData) : S.Modules :=
  (Scheme.Modules.pushforward I.subschemeι).obj
    (SheafOfModules.unit I.subscheme.ringCatSheaf)

/-- The structure sheaf of `S`, viewed as a module over itself. -/
noncomputable def ambientStructureSheaf (S : Scheme.{u}) : S.Modules :=
  SheafOfModules.unit S.ringCatSheaf

/-- The structure sheaf of the target of a morphism of schemes mapping to the direct image of
the structure sheaf of its source. -/
noncomputable def ambientToPushforward {Z S : Scheme.{u}} (i : Z ⟶ S) :
    ambientStructureSheaf S ⟶ (Scheme.Modules.pushforward i).obj (ambientStructureSheaf Z) :=
  SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom

/-- The ambient structure sheaf mapping to the pushed-forward structure sheaf of the closed
subscheme cut out by `I`. -/
noncomputable def ambientToClosedSubscheme {S : Scheme.{u}} (I : S.IdealSheafData) :
    ambientStructureSheaf S ⟶ closedSubschemeStructureSheaf I :=
  ambientToPushforward I.subschemeι

/-- The sections of a composite of morphisms of modules are the composite of the sections. -/
lemma comp_app_apply {S : Scheme.{u}} {M N K : S.Modules} (f : M ⟶ N) (g : N ⟶ K)
    (U : S.Opens) (m : Γ(M, U)) : (f ≫ g).app U m = g.app U (f.app U m) := rfl

private lemma neg_app_apply {S : Scheme.{u}} {M N : S.Modules} (f : M ⟶ N) (U : S.Opens)
    (m : Γ(M, U)) : (-f).app U m = -(f.app U m) := rfl

/-- The sections of the zero morphism vanish. -/
lemma app_apply_of_eq_zero {S : Scheme.{u}} {M N : S.Modules} {f : M ⟶ N} (hf : f = 0)
    (U : S.Opens) (m : Γ(M, U)) : f.app U m = 0 := by
  subst hf
  simp

private alias app_apply_eq_zero := app_apply_of_eq_zero

/-- The morphism `eqToHom e` sends a section `n` to any section `k` heterogeneously equal to it. -/
lemma eqToHom_app_heq {S : Scheme.{u}} {N K : S.Modules} (e : N = K) (U : S.Opens)
    (n : Γ(N, U)) (k : Γ(K, U)) (hk : HEq n k) : (eqToHom e).app U n = k := by
  subst e
  exact eq_of_heq hk

/-- Equal morphisms of schemes have heterogeneously equal maps on sections. -/
lemma heq_scheme_app {X Y : Scheme.{u}} {f g : X ⟶ Y} (hfg : f = g) (U : Y.Opens)
    (a : Γ(Y, U)) : HEq (f.app U a) (g.app U a) := by
  subst hfg
  rfl

/-- The comparison isomorphism `Scheme.Modules.pushforwardComp p q` is the identity on sections. -/
lemma pushforwardComp_app_apply {X Y Z : Scheme.{u}} (p : X ⟶ Y) (q : Y ⟶ Z)
    (M : X.Modules) (U : Z.Opens)
    (m : Γ((Scheme.Modules.pushforward q).obj ((Scheme.Modules.pushforward p).obj M), U)) :
    ((Scheme.Modules.pushforwardComp p q).hom.app M).app U m = m := rfl

/-- On sections over `U`, the direct image of `φ` along `q` is `φ` on sections over `q ⁻¹ᵁ U`. -/
lemma pushforward_map_app_apply {X Z : Scheme.{u}} (q : X ⟶ Z) {M N : X.Modules}
    (φ : M ⟶ N) (U : Z.Opens) (m : Γ((Scheme.Modules.pushforward q).obj M, U)) :
    ((Scheme.Modules.pushforward q).map φ).app U m = φ.app (q ⁻¹ᵁ U) m := rfl

private lemma unitToPushforward_app_apply {X Z : Scheme.{u}} (r : X ⟶ Z) (U : Z.Opens)
    (a : Γ(Z, U)) :
    Scheme.Modules.Hom.app (M := ambientStructureSheaf Z)
      (N := (Scheme.Modules.pushforward r).obj (SheafOfModules.unit X.ringCatSheaf))
      (SheafOfModules.unitToPushforwardObjUnit r.toRingCatSheafHom) U a = r.app U a := rfl

/-- On sections over an open set, `ambientToClosedSubscheme` is the structure-sheaf map of
the closed immersion of the subscheme. -/
theorem ambientToClosedSubscheme_app_apply {S : Scheme.{u}} (I : S.IdealSheafData)
    (U : S.Opens) (a : Γ(S, U)) :
    (ambientToClosedSubscheme I).app U a = I.subschemeι.app U a := rfl

/-- A morphism of modules which vanishes on sections over every affine open is zero. -/
lemma hom_eq_zero_of_app_affineOpens {S : Scheme.{u}} {M N : S.Modules} (f : M ⟶ N)
    (h : ∀ (U : S.affineOpens) (m : Γ(M, U.1)), f.app U.1 m = 0) : f = 0 := by
  apply Scheme.Modules.hom_ext
  intro U
  ext m
  refine N.isSheaf.section_ext (U := op U) ?_
  intro x hx
  obtain ⟨V, hVmem, hxV, hVU⟩ := (Opens.isBasis_iff_nbhd.1 S.isBasis_affineOpens) hx
  refine ⟨V, hVU, hxV, ?_⟩
  have hnat := ConcreteCategory.congr_hom (f.mapPresheaf.naturality (homOfLE hVU).op) m
  simp only [Scheme.Modules.mapPresheaf_app, unop_op, ConcreteCategory.comp_apply] at hnat
  have hR : N.presheaf.map (homOfLE hVU).op ((0 : M ⟶ N).app U m) = 0 := by simp
  rw [hR, ← hnat]
  exact h ⟨V, hVmem⟩ _

private alias module_hom_eq_zero_of_affine := hom_eq_zero_of_app_affineOpens

/-- A morphism of modules whose underlying map of sheaves of abelian groups is locally surjective
is an epimorphism. -/
lemma epi_of_isLocallySurjective_toSheaf_map {S : Scheme.{u}} {M N : S.Modules} (f : M ⟶ N)
    (hf : Presheaf.IsLocallySurjective (Opens.grothendieckTopology S)
      ((SheafOfModules.toSheaf S.ringCatSheaf).map f).hom) : Epi f := by
  let : Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf S.ringCatSheaf).map f) :=
    (Sheaf.isLocallySurjective_sheafToPresheaf_map_iff _).2 hf
  exact (SheafOfModules.toSheaf S.ringCatSheaf).epi_of_epi_map
    (Sheaf.epi_of_isLocallySurjective _)

private alias epi_of_isLocallySurjective_app := epi_of_isLocallySurjective_toSheaf_map

/-- **The comparison map of a closed immersion is an epimorphism.** On sections over an affine
open the map is the surjection of the closed immersion, and the affine opens form a basis, so
the map is locally surjective. -/
theorem epi_ambientToPushforward {Z S : Scheme.{u}} (i : Z ⟶ S) [IsClosedImmersion i] :
    Epi (ambientToPushforward i) := by
  apply epi_of_isLocallySurjective_app
  refine (TopCat.Presheaf.isLocallySurjective_iff _).2 ?_
  intro U t x hx
  obtain ⟨V, hVmem, hxV, hVU⟩ := (Opens.isBasis_iff_nbhd.1 S.isBasis_affineOpens) hx
  refine ⟨V, hVU, ?_, hxV⟩
  obtain ⟨s, hs⟩ := Scheme.Hom.app_surjective i V hVmem (t |_ V)
  exact ⟨s, hs⟩

/-- The map from the ambient structure sheaf to that of a closed subscheme is an epimorphism. -/
lemma ambientToClosedSubscheme_epi {S : Scheme.{u}} (I : S.IdealSheafData) :
    Epi (ambientToClosedSubscheme I) := epi_ambientToPushforward I.subschemeι

private alias epi_ambientToClosedSubscheme := ambientToClosedSubscheme_epi

/-- Over an affine open, a section of the ambient structure sheaf dies in the structure
sheaf of the closed subscheme exactly when it lies in the defining ideal. -/
lemma ambientToClosedSubscheme_app_eq_zero_iff_mem_ideal {S : Scheme.{u}} (I : S.IdealSheafData)
    (U : S.affineOpens) (a : Γ(S, U.1)) :
    (ambientToClosedSubscheme I).app U.1 a = 0 ↔ a ∈ I.ideal U := by
  rw [← I.ker_subschemeι_app U]
  exact Iff.rfl

private alias ambientToClosedSubscheme_app_eq_zero_iff := ambientToClosedSubscheme_app_eq_zero_iff_mem_ideal

/-- Sections of the ambient structure sheaf lying in `I.ideal U` die under any map out of
`ambientToClosedSubscheme I`. -/
private lemma app_comp_ambientToClosedSubscheme_eq_zero_of_mem_ideal {S : Scheme.{u}}
    (I : S.IdealSheafData) {T : S.Modules} (f : closedSubschemeStructureSheaf I ⟶ T)
    (U : S.affineOpens) {b : Γ(S, U.1)} (hb : b ∈ I.ideal U) :
    (ambientToClosedSubscheme I ≫ f).app U.1 b = 0 := by
  refine (comp_app_apply (ambientToClosedSubscheme I) f U.1 b).trans ?_
  rw [(ambientToClosedSubscheme_app_eq_zero_iff I U b).2 hb]
  exact map_zero _

/-- If `a ≫ ambientToClosedSubscheme I = 0`, every section of `a` lies in `I.ideal U`. -/
private lemma mem_ideal_of_comp_ambientToClosedSubscheme_eq_zero {S : Scheme.{u}}
    {I : S.IdealSheafData} {T : S.Modules} {a : T ⟶ ambientStructureSheaf S}
    (h : a ≫ ambientToClosedSubscheme I = 0) (U : S.affineOpens) (m : Γ(T, U.1)) :
    a.app U.1 m ∈ I.ideal U :=
  (ambientToClosedSubscheme_app_eq_zero_iff I U _).1
    ((comp_app_apply a _ U.1 m).symm.trans (app_apply_eq_zero h U.1 m))

/-- The canonical restriction map on pushed-forward structure sheaves associated to
`I ≤ J`, equivalently to the closed immersion of the subscheme cut out by `J` into the
one cut out by `I`. -/
noncomputable def closedSubschemeRestriction {S : Scheme.{u}}
    {I J : S.IdealSheafData} (h : I ≤ J) :
    closedSubschemeStructureSheaf I ⟶ closedSubschemeStructureSheaf J :=
  (Scheme.Modules.pushforward I.subschemeι).map
      (SheafOfModules.unitToPushforwardObjUnit
        (Scheme.IdealSheafData.inclusion h).toRingCatSheafHom) ≫
    (Scheme.Modules.pushforwardComp
      (Scheme.IdealSheafData.inclusion h) I.subschemeι).hom.app _ ≫
    eqToHom (by rw [Scheme.IdealSheafData.inclusion_subschemeι h])

/-- On sections over `U`, `closedSubschemeRestriction h` is the map of the closed immersion
`inclusion h` on sections over `I.subschemeι ⁻¹ᵁ U`. -/
private lemma closedSubschemeRestriction_app_apply {S : Scheme.{u}} {I J : S.IdealSheafData}
    (h : I ≤ J) (U : S.Opens) (x : Γ(closedSubschemeStructureSheaf I, U))
    (k : Γ(closedSubschemeStructureSheaf J, U))
    (hk : HEq ((Scheme.IdealSheafData.inclusion h).app (I.subschemeι ⁻¹ᵁ U) x) k) :
    (closedSubschemeRestriction h).app U x = k := by
  rw [closedSubschemeRestriction]
  refine (comp_app_apply _ _ U x).trans ((comp_app_apply _ _ U _).trans ?_)
  exact eqToHom_app_heq _ U _ _ hk

/-- **On global sections the restriction between nested closed subschemes is the restriction
along their inclusion.**  For `I ≤ J`, that is for the subscheme cut out by `J` contained in the
one cut out by `I`, the map `closedSubschemeRestriction h` of modules on the ambient scheme acts
on sections over the whole space as the map `Γ(I.subscheme, 𝒪) ⟶ Γ(J.subscheme, 𝒪)` of the
closed immersion `Scheme.IdealSheafData.inclusion h`; the two agree because the open sets
involved are the preimages of the whole space, which is the whole space. -/
theorem closedSubschemeRestriction_app_top {S : Scheme.{u}} {I J : S.IdealSheafData} (h : I ≤ J)
    (x : Γ(closedSubschemeStructureSheaf I, ⊤)) :
    (closedSubschemeRestriction h).app ⊤ x =
      (Scheme.IdealSheafData.inclusion h).appTop.hom x :=
  closedSubschemeRestriction_app_apply h ⊤ x _ HEq.rfl

/-- Restriction between nested closed subschemes is compatible with the canonical maps out
of the ambient structure sheaf. -/
lemma ambientToClosedSubscheme_comp_closedSubschemeRestriction {S : Scheme.{u}}
    {I J : S.IdealSheafData} (h : I ≤ J) :
    ambientToClosedSubscheme I ≫ closedSubschemeRestriction h = ambientToClosedSubscheme J := by
  apply Scheme.Modules.hom_ext
  intro U
  ext a
  refine (comp_app_apply _ _ U a).trans (closedSubschemeRestriction_app_apply h U _ _ ?_)
  exact (heq_of_eq (ConcreteCategory.congr_hom (Scheme.Hom.comp_app
    (Scheme.IdealSheafData.inclusion h) I.subschemeι U) a).symm).trans
    (heq_scheme_app (Scheme.IdealSheafData.inclusion_subschemeι h) U a)

private alias ambientToClosedSubscheme_comp_restriction := ambientToClosedSubscheme_comp_closedSubschemeRestriction

/-- `ambientToClosedSubscheme_comp_closedSubschemeRestriction`, followed by a further morphism. -/
lemma ambientToClosedSubscheme_comp_closedSubschemeRestriction_assoc {S : Scheme.{u}}
    {I J : S.IdealSheafData} (h : I ≤ J) {T : S.Modules}
    (g : closedSubschemeStructureSheaf J ⟶ T) :
    ambientToClosedSubscheme I ≫ closedSubschemeRestriction h ≫ g =
      ambientToClosedSubscheme J ≫ g := by
  rw [← Category.assoc, ambientToClosedSubscheme_comp_restriction]

private alias ambientToClosedSubscheme_comp_restriction_assoc := ambientToClosedSubscheme_comp_closedSubschemeRestriction_assoc

/-- The pair of canonical maps from the structure sheaf of the scheme-theoretic union to
the two pushed-forward structure sheaves. -/
noncomputable def unionToBiprod {S : Scheme.{u}} (I J : S.IdealSheafData) :
    closedSubschemeStructureSheaf (I ⊓ J) ⟶
      closedSubschemeStructureSheaf I ⊞ closedSubschemeStructureSheaf J :=
  biprod.lift
    (closedSubschemeRestriction (I := I ⊓ J) (J := I) inf_le_left)
    (closedSubschemeRestriction (I := I ⊓ J) (J := J) inf_le_right)

/-- The difference of the two canonical maps from the pushed-forward structure sheaves to
the structure sheaf of the scheme-theoretic intersection. -/
noncomputable def biprodToIntersection {S : Scheme.{u}} (I J : S.IdealSheafData) :
    closedSubschemeStructureSheaf I ⊞ closedSubschemeStructureSheaf J ⟶
      closedSubschemeStructureSheaf (I ⊔ J) :=
  biprod.desc
    (closedSubschemeRestriction (I := I) (J := I ⊔ J) le_sup_left)
    (-closedSubschemeRestriction (I := J) (J := I ⊔ J) le_sup_right)

/-- The map to the scheme-theoretic union followed by the pair of restrictions is the pair of maps
to the two closed subschemes. -/
lemma ambientToClosedSubscheme_inf_comp_unionToBiprod {S : Scheme.{u}}
    (I J : S.IdealSheafData) :
    ambientToClosedSubscheme (I ⊓ J) ≫ unionToBiprod I J =
      biprod.lift (ambientToClosedSubscheme I) (ambientToClosedSubscheme J) := by
  refine biprod.hom_ext _ _ ?_ ?_ <;>
    simp only [unionToBiprod, Category.assoc, biprod.lift_fst, biprod.lift_snd,
      ambientToClosedSubscheme_comp_restriction]

private alias ambientToClosedSubscheme_comp_unionToBiprod := ambientToClosedSubscheme_inf_comp_unionToBiprod

private lemma unionToBiprod_comp_biprodToIntersection {S : Scheme.{u}} (I J : S.IdealSheafData) :
    unionToBiprod I J ≫ biprodToIntersection I J = 0 := by
  have : Epi (ambientToClosedSubscheme (I ⊓ J)) := epi_ambientToClosedSubscheme (I ⊓ J)
  apply (cancel_epi (ambientToClosedSubscheme (I ⊓ J))).mp
  rw [unionToBiprod, biprodToIntersection, biprod.lift_desc, Preadditive.comp_neg,
    Preadditive.comp_add, Preadditive.comp_neg,
    ambientToClosedSubscheme_comp_restriction_assoc,
    ambientToClosedSubscheme_comp_restriction_assoc,
    ambientToClosedSubscheme_comp_restriction,
    ambientToClosedSubscheme_comp_restriction, add_neg_cancel, comp_zero]

/-- **The second arrow of the union sequence splits off the comparison map of the
intersection.** Restricting a function from the ambient scheme to the first closed subscheme and
then taking the difference of the two restrictions is restriction to the intersection, the
second restriction contributing nothing because it is applied to a global function. -/
theorem ambientToClosedSubscheme_inl_comp_biprodToIntersection {S : Scheme.{u}}
    (I J : S.IdealSheafData) :
    (ambientToClosedSubscheme I ≫ biprod.inl) ≫ biprodToIntersection I J =
      ambientToClosedSubscheme (I ⊔ J) := by
  rw [biprodToIntersection, Category.assoc, biprod.inl_desc,
    ambientToClosedSubscheme_comp_restriction]

private lemma epi_biprodToIntersection {S : Scheme.{u}} (I J : S.IdealSheafData) :
    Epi (biprodToIntersection I J) :=
  have : Epi (ambientToClosedSubscheme (I ⊔ J)) := epi_ambientToClosedSubscheme (I ⊔ J)
  epi_of_epi_fac (ambientToClosedSubscheme_inl_comp_biprodToIntersection I J)

private lemma mono_of_epi_comp_cancel_zero {S : Scheme.{u}} {A D E : S.Modules}
    (q : A ⟶ D) [Epi q] (f : D ⟶ E)
    (h : ∀ {T : S.Modules} (a : T ⟶ A), a ≫ q ≫ f = 0 → a ≫ q = 0) : Mono f := by
  apply Preadditive.mono_of_cancel_zero
  intro T a ha
  apply (cancel_epi (pullback.fst a q)).mp
  rw [comp_zero, pullback.condition]
  apply h
  rw [← pullback.condition_assoc, ha, comp_zero]

/-- The first arrow of the union sequence is a monomorphism. -/
lemma unionToBiprod_mono {S : Scheme.{u}} (I J : S.IdealSheafData) :
    Mono (unionToBiprod I J) := by
  have : Epi (ambientToClosedSubscheme (I ⊓ J)) := epi_ambientToClosedSubscheme (I ⊓ J)
  apply mono_of_epi_comp_cancel_zero (ambientToClosedSubscheme (I ⊓ J))
  intro T a ha
  rw [ambientToClosedSubscheme_comp_unionToBiprod] at ha
  have hy : a ≫ ambientToClosedSubscheme I = 0 := by
    have h₁ := congrArg (fun t => t ≫ biprod.fst) ha
    simpa only [Category.assoc, biprod.lift_fst, zero_comp] using h₁
  have hz : a ≫ ambientToClosedSubscheme J = 0 := by
    have h₂ := congrArg (fun t => t ≫ biprod.snd) ha
    simpa only [Category.assoc, biprod.lift_snd, zero_comp] using h₂
  apply module_hom_eq_zero_of_affine
  intro U m
  refine (comp_app_apply a (ambientToClosedSubscheme (I ⊓ J)) U.1 m).trans ?_
  refine (ambientToClosedSubscheme_app_eq_zero_iff (I ⊓ J) U _).2 ?_
  rw [Scheme.IdealSheafData.ideal_inf]
  exact ⟨mem_ideal_of_comp_ambientToClosedSubscheme_eq_zero hy U m,
    mem_ideal_of_comp_ambientToClosedSubscheme_eq_zero hz U m⟩

private alias mono_unionToBiprod := unionToBiprod_mono

private lemma exists_desc_biprodToIntersection {S : Scheme.{u}} (I J : S.IdealSheafData)
    {T : S.Modules}
    (r : closedSubschemeStructureSheaf I ⊞ closedSubschemeStructureSheaf J ⟶ T)
    (hr : unionToBiprod I J ≫ r = 0) :
    ∃ l, biprodToIntersection I J ≫ l = r := by
  have hepiI : Epi (ambientToClosedSubscheme I) := epi_ambientToClosedSubscheme I
  have hepiJ : Epi (ambientToClosedSubscheme J) := epi_ambientToClosedSubscheme J
  have hepiS : Epi (ambientToClosedSubscheme (I ⊔ J)) := epi_ambientToClosedSubscheme (I ⊔ J)
  have ht : ambientToClosedSubscheme I ≫ biprod.inl ≫ r =
      -(ambientToClosedSubscheme J ≫ biprod.inr ≫ r) := by
    have hh := congrArg (fun k => ambientToClosedSubscheme (I ⊓ J) ≫ k) hr
    rw [← Category.assoc, ambientToClosedSubscheme_comp_unionToBiprod] at hh
    have hsum : ambientToClosedSubscheme I ≫ biprod.inl ≫ r +
        ambientToClosedSubscheme J ≫ biprod.inr ≫ r = 0 := by
      simpa only [biprod.lift_eq, Preadditive.add_comp, Category.assoc, comp_zero] using hh
    exact add_eq_zero_iff_eq_neg.mp hsum
  have hn : kernel.ι (ambientToClosedSubscheme (I ⊔ J)) ≫
      (ambientToClosedSubscheme I ≫ biprod.inl ≫ r) = 0 := by
    apply module_hom_eq_zero_of_affine
    intro U m
    have key : ∀ b : Γ(S, U.1), b ∈ (I ⊔ J).ideal U →
        (ambientToClosedSubscheme I ≫ biprod.inl ≫ r).app U.1 b = 0 := by
      intro b hbmem
      rw [Scheme.IdealSheafData.ideal_sup] at hbmem
      obtain ⟨c, hc, d, hd, hcd⟩ := Submodule.mem_sup.mp hbmem
      have htc := app_comp_ambientToClosedSubscheme_eq_zero_of_mem_ideal I (biprod.inl ≫ r) U hc
      have hd1 := app_comp_ambientToClosedSubscheme_eq_zero_of_mem_ideal J (biprod.inr ≫ r) U hd
      have htd : (ambientToClosedSubscheme I ≫ biprod.inl ≫ r).app U.1 d = 0 := by
        rw [ht]
        refine (neg_app_apply (ambientToClosedSubscheme J ≫ biprod.inr ≫ r) U.1 d).trans ?_
        rw [hd1, neg_zero]
      have hsplit : ∀ x y : Γ(ambientStructureSheaf S, U.1),
          (ambientToClosedSubscheme I ≫ biprod.inl ≫ r).app U.1 (x + y) =
            (ambientToClosedSubscheme I ≫ biprod.inl ≫ r).app U.1 x +
              (ambientToClosedSubscheme I ≫ biprod.inl ≫ r).app U.1 y := fun x y => by simp
      refine (congrArg ((ambientToClosedSubscheme I ≫ biprod.inl ≫ r).app U.1)
        hcd).symm.trans ((hsplit c d).trans ?_)
      rw [htc, htd, add_zero]
    refine (comp_app_apply (kernel.ι (ambientToClosedSubscheme (I ⊔ J)))
      (ambientToClosedSubscheme I ≫ biprod.inl ≫ r) U.1 m).trans (key _ ?_)
    exact mem_ideal_of_comp_ambientToClosedSubscheme_eq_zero (kernel.condition _) U m
  refine ⟨Abelian.epiDesc (ambientToClosedSubscheme (I ⊔ J))
    (ambientToClosedSubscheme I ≫ biprod.inl ≫ r) hn, ?_⟩
  have hl := Abelian.comp_epiDesc (ambientToClosedSubscheme (I ⊔ J))
    (ambientToClosedSubscheme I ≫ biprod.inl ≫ r) hn
  refine biprod.hom_ext' _ _ ?_ ?_
  · apply (cancel_epi (ambientToClosedSubscheme I)).mp
    rw [biprodToIntersection, biprod.inl_desc_assoc, ← Category.assoc,
      ambientToClosedSubscheme_comp_restriction, hl]
  · apply (cancel_epi (ambientToClosedSubscheme J)).mp
    rw [biprodToIntersection, biprod.inr_desc_assoc, Preadditive.neg_comp,
      Preadditive.comp_neg, ← Category.assoc, ambientToClosedSubscheme_comp_restriction,
      hl, ht, neg_neg]

/-- **Stacks Project, Tag 0C4J.** The canonical sequence of structure sheaves of the
scheme-theoretic union, the two closed subschemes and their scheme-theoretic intersection,
whose last nonzero arrow is the difference of the two restriction maps, is short exact. -/
@[stacks 0C4J "union_exact_sequence"]
theorem unionIntersection_shortExact {S : Scheme.{u}} (I J : S.IdealSheafData) :
    ∃ zero : unionToBiprod I J ≫ biprodToIntersection I J = 0,
      (ShortComplex.mk (unionToBiprod I J) (biprodToIntersection I J) zero).ShortExact := by
  have : Mono (unionToBiprod I J) := mono_unionToBiprod I J
  have : Epi (biprodToIntersection I J) := epi_biprodToIntersection I J
  have hzero : unionToBiprod I J ≫ biprodToIntersection I J = 0 :=
    unionToBiprod_comp_biprodToIntersection I J
  refine ⟨hzero, { exact := ?_ }⟩
  have : (ShortComplex.mk (unionToBiprod I J) (biprodToIntersection I J) hzero).HasHomology :=
    ShortComplex.HasHomology.mk' (ShortComplex.HomologyData.ofAbelian
      (ShortComplex.mk (unionToBiprod I J) (biprodToIntersection I J) hzero))
  apply ShortComplex.exact_of_g_is_cokernel
  apply CokernelCofork.IsColimit.ofπ'
  intro T r hr
  exact ⟨(exists_desc_biprodToIntersection I J r hr).choose,
    (exists_desc_biprodToIntersection I J r hr).choose_spec⟩

/-- **The comparison maps compose.** Pushing the comparison map of `f` forward along `g` and
prefixing the comparison map of `g` gives the comparison map of `f ≫ g`, up to the
identification of `g_* f_*` with `(f ≫ g)_*`. On sections all three maps are maps of
structure sheaves over the same open set, so the identity holds on the nose. -/
theorem ambientToPushforward_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ambientToPushforward g ≫ (Scheme.Modules.pushforward g).map (ambientToPushforward f) ≫
        (Scheme.Modules.pushforwardComp f g).hom.app (ambientStructureSheaf X) =
      ambientToPushforward (f ≫ g) := by
  apply Scheme.Modules.hom_ext
  intro U
  rfl

/-- **A morphism carries the comparison map of `f` to an epimorphism as soon as `f ≫ g` is a
closed immersion.** The comparison map of `f ≫ g` is an epimorphism, and it factors through
the pushed-forward comparison map of `f`. -/
theorem epi_pushforward_map_ambientToPushforward {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsClosedImmersion (f ≫ g)] :
    Epi ((Scheme.Modules.pushforward g).map (ambientToPushforward f)) := by
  have : Epi (ambientToPushforward (f ≫ g)) := epi_ambientToPushforward (f ≫ g)
  have hfac : Epi ((Scheme.Modules.pushforward g).map (ambientToPushforward f) ≫
      (Scheme.Modules.pushforwardComp f g).hom.app (ambientStructureSheaf X)) :=
    epi_of_epi_fac (ambientToPushforward_comp f g)
  have hinv : (Scheme.Modules.pushforward g).map (ambientToPushforward f) =
      ((Scheme.Modules.pushforward g).map (ambientToPushforward f) ≫
          (Scheme.Modules.pushforwardComp f g).hom.app (ambientStructureSheaf X)) ≫
        (Scheme.Modules.pushforwardComp f g).inv.app (ambientStructureSheaf X) := by
    simp
  rw [hinv]
  infer_instance

/-- **A morphism of schemes carries the second arrow of the union sequence of
[Stacks, Tag 0C4J] to an epimorphism whenever it maps the scheme-theoretic intersection of the
two closed subschemes into the target as a closed immersion.** Surjectivity of the difference of
the two restrictions is already witnessed on the first summand alone, by functions coming from
the ambient scheme, and that witness survives the pushforward. -/
theorem epi_pushforward_map_biprodToIntersection {S T : Scheme.{u}} (I J : S.IdealSheafData)
    (g : S ⟶ T) [IsClosedImmersion ((I ⊔ J).subschemeι ≫ g)] :
    Epi ((Scheme.Modules.pushforward g).map (biprodToIntersection I J)) := by
  have : Epi ((Scheme.Modules.pushforward g).map (ambientToClosedSubscheme (I ⊔ J))) :=
    epi_pushforward_map_ambientToPushforward (I ⊔ J).subschemeι g
  refine epi_of_epi_fac (f := (Scheme.Modules.pushforward g).map
      (ambientToClosedSubscheme I ≫ biprod.inl))
    (h := (Scheme.Modules.pushforward g).map (ambientToClosedSubscheme (I ⊔ J))) ?_
  rw [← Functor.map_comp, ambientToClosedSubscheme_inl_comp_biprodToIntersection]

/-- **The comparison map of an isomorphism of schemes is an isomorphism.** On sections over an
open set it is the map on functions of the isomorphism. -/
theorem isIso_ambientToPushforward {Z S : Scheme.{u}} (i : Z ⟶ S) [IsIso i] :
    IsIso (ambientToPushforward i) := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro U
  show IsIso (((forget₂ CommRingCat RingCat) ⋙ forget₂ RingCat AddCommGrpCat).map (i.app U))
  infer_instance

/-- **The structure sheaf of the closed subscheme cut out by the zero ideal sheaf is the ambient
structure sheaf.** The closed immersion of that subscheme is an isomorphism of schemes, so its
comparison map is an isomorphism on sections over every open set. -/
noncomputable def closedSubschemeStructureSheafBotIso (S : Scheme.{u}) :
    closedSubschemeStructureSheaf (⊥ : S.IdealSheafData) ≅ ambientStructureSheaf S :=
  have := isIso_ambientToPushforward (⊥ : S.IdealSheafData).subschemeι
  (asIso (ambientToPushforward (⊥ : S.IdealSheafData).subschemeι)).symm

end AlgebraicGeometry.Scheme.IdealSheafData
