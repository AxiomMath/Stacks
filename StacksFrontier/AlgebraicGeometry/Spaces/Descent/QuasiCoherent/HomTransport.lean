module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.Canonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.FamilyPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.HomDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.SingleMorphismHomDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.EquivariantQuasicoherentPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardCompIsoAssoc
public import StacksFrontier.CategoryTheory.Functor.DescentOfMaps

/-!
# Inverse images of morphisms of inverse images

Let `M`, `N` be modules on an algebraic space `A`. For a morphism `p : P ⟶ A` a morphism
`ψ : p^*M ⟶ p^*N` has an inverse image along any `g : T ⟶ P`, which read through the comparisons
of Stacks 03LU is a morphism `v^*M ⟶ v^*N` for `v = g ≫ p`. These inverse images compose, and
the condition of Stacks 04W5 at a pair of morphisms with equal composites is the equality of the
two inverse images. Descent of morphisms along a surjective étale morphism (Stacks 04W6) then
only needs the condition at the kernel pair.

## Main definitions

* `AlgebraicGeometry.Space.QuasiCoherentDescent.homTransport`: the inverse image of `ψ`.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.homRebase`: a morphism `g^*p^*M ⟶ g^*p^*N` read as
  a morphism `v^*M ⟶ v^*N`.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.homTransport_homTransport`: composition.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.exists_homTransport_eq_of_isPullback`: descent of
  morphisms along a surjective étale morphism, compatible at its kernel pair.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : AlgebraicSpaces B S hS} (M N : Modules.{u, u} B S hS A.1 A.2)

/-- A morphism `g^*p^*M ⟶ g^*p^*N`, read as a morphism `v^*M ⟶ v^*N` for `v = g ≫ p`. -/
def homRebase {P T : AlgebraicSpaces B S hS} (g : T ⟶ P) {p : P ⟶ A} {v : T ⟶ A}
    (hv : g ≫ p = v)
    (ψ : (modulePullback B S hS g).obj ((modulePullback B S hS p).obj M) ⟶
      (modulePullback B S hS g).obj ((modulePullback B S hS p).obj N)) :
    (modulePullback B S hS v).obj M ⟶ (modulePullback B S hS v).obj N :=
  (pullbackComparison B S hS g p v hv M).hom ≫ ψ ≫ (pullbackComparison B S hS g p v hv N).inv

/-- The inverse image along `g : T ⟶ P` of a morphism `ψ : p^*M ⟶ p^*N`, read as a morphism
`v^*M ⟶ v^*N` for `v = g ≫ p` through the comparisons of Stacks 03LU. -/
def homTransport {P T : AlgebraicSpaces B S hS} (g : T ⟶ P) {p : P ⟶ A} {v : T ⟶ A}
    (hv : g ≫ p = v) (ψ : (modulePullback B S hS p).obj M ⟶ (modulePullback B S hS p).obj N) :
    (modulePullback B S hS v).obj M ⟶ (modulePullback B S hS v).obj N :=
  homRebase M N g hv ((modulePullback B S hS g).map ψ)

variable {M N}

/-- The defining formula of `homRebase`. -/
theorem homRebase_def {P T : AlgebraicSpaces B S hS} (g : T ⟶ P) {p : P ⟶ A} {v : T ⟶ A}
    (hv : g ≫ p = v)
    (ψ : (modulePullback B S hS g).obj ((modulePullback B S hS p).obj M) ⟶
      (modulePullback B S hS g).obj ((modulePullback B S hS p).obj N)) :
    homRebase M N g hv ψ =
      (pullbackComparison B S hS g p v hv M).hom ≫ ψ ≫ (pullbackComparison B S hS g p v hv N).inv :=
  rfl

/-- The defining formula of `homTransport`. -/
theorem homTransport_def {P T : AlgebraicSpaces B S hS} (g : T ⟶ P) {p : P ⟶ A} {v : T ⟶ A}
    (hv : g ≫ p = v) (ψ : (modulePullback B S hS p).obj M ⟶ (modulePullback B S hS p).obj N) :
    homTransport M N g hv ψ = homRebase M N g hv ((modulePullback B S hS g).map ψ) :=
  rfl

/-- Reading a morphism `g^*p^*M ⟶ g^*p^*N` as a morphism `v^*M ⟶ v^*N` is injective. -/
theorem homRebase_injective {P T : AlgebraicSpaces B S hS} (g : T ⟶ P) {p : P ⟶ A}
    {v : T ⟶ A} (hv : g ≫ p = v) : Function.Injective (homRebase M N g hv) := by
  intro ψ₁ ψ₂ h
  rw [homRebase_def, homRebase_def] at h
  simpa using h

/-- The inverse image of the inverse image of a morphism of modules is its inverse image. -/
theorem homTransport_map {P T : AlgebraicSpaces B S hS} (g : T ⟶ P) {p : P ⟶ A} {v : T ⟶ A}
    (hv : g ≫ p = v) (χ : M ⟶ N) :
    homTransport M N g hv ((modulePullback B S hS p).map χ) = (modulePullback B S hS v).map χ := by
  rw [homTransport_def, homRebase_def, pullbackComparison_inv_naturality B S hS,
    Iso.hom_inv_id_assoc]

/-- The comparison of Stacks 03LU at a factorization, written with the comparison of iterated
inverse images. -/
theorem pullbackComparison_hom_eq {P T : AlgebraicSpaces B S hS} (g : T ⟶ P) (p : P ⟶ A)
    {v : T ⟶ A} (hv : g ≫ p = v) (M : Modules.{u, u} B S hS A.1 A.2) :
    (pullbackComparison B S hS g p v hv M).hom =
      eqToHom (congrArg (fun q : T ⟶ A => (modulePullback B S hS q).obj M) hv.symm) ≫
        (modulePullbackCompIso B S hS g p).inv.app M := by
  subst hv
  simp [pullbackComparison]

/-- The comparisons of Stacks 03LU for a factorization through two morphisms compose. -/
theorem pullbackComparison_trans_mapIso {P T T' : AlgebraicSpaces B S hS} (w : T' ⟶ T)
    (g : T ⟶ P) (p : P ⟶ A) {v : T ⟶ A} (hv : g ≫ p = v) {v' : T' ⟶ A} (hv' : w ≫ v = v')
    (hv'' : (w ≫ g) ≫ p = v') (M : Modules.{u, u} B S hS A.1 A.2) :
    pullbackComparison B S hS w v v' hv' M ≪≫
        (modulePullback B S hS w).mapIso (pullbackComparison B S hS g p v hv M) =
      pullbackComparison B S hS (w ≫ g) p v' hv'' M ≪≫
        pullbackComparison B S hS w g (w ≫ g) rfl ((modulePullback B S hS p).obj M) := by
  subst hv hv'
  apply Iso.ext
  have h := congrArg Iso.hom (mapIso_pullbackComparison B S hS w g p M)
  simp only [Functor.mapIso_hom, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv] at h
  simp only [Iso.trans_hom, Functor.mapIso_hom]
  rw [h, pullbackComparison_rfl, pullbackComparison_rfl, pullbackComparison_rfl,
    pullbackComparison_hom_eq]
  simp only [Iso.symm_hom, Iso.app_inv, Iso.inv_hom_id_app_assoc]
  exact (Category.id_comp _).symm

/-- Conjugating the image of a morphism by two factorizations of the same isomorphisms. -/
private theorem conj_map_eq_of_comp_eq {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {X₁ X₂ Y₁ Y₂ : C} {V₁ V₂ Z₁ Z₂ : D} (α : V₁ ≅ F.obj X₁) (β : X₁ ≅ X₂) (γ : Y₁ ≅ Y₂)
    (δ : V₂ ≅ F.obj Y₁) (ε : V₁ ≅ Z₁) (ζ : Z₁ ≅ F.obj X₂) (η : Z₂ ≅ F.obj Y₂) (θ : V₂ ≅ Z₂)
    (ψ : X₂ ⟶ Y₂) (hM : α.hom ≫ F.map β.hom = ε.hom ≫ ζ.hom)
    (hN : F.map γ.inv ≫ δ.inv = η.inv ≫ θ.inv) :
    α.hom ≫ F.map (β.hom ≫ ψ ≫ γ.inv) ≫ δ.inv = ε.hom ≫ (ζ.hom ≫ F.map ψ ≫ η.inv) ≫ θ.inv := by
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hM, hN]

/-- **Inverse images of rebased morphisms.** -/
theorem homTransport_homRebase {P T T' : AlgebraicSpaces B S hS} (w : T' ⟶ T) (g : T ⟶ P)
    {p : P ⟶ A} {v : T ⟶ A} (hv : g ≫ p = v) {v' : T' ⟶ A} (hv' : w ≫ v = v') {g' : T' ⟶ P}
    (hw : w ≫ g = g') (hv'' : g' ≫ p = v')
    (ψ : (modulePullback B S hS g).obj ((modulePullback B S hS p).obj M) ⟶
      (modulePullback B S hS g).obj ((modulePullback B S hS p).obj N)) :
    homTransport M N w hv' (homRebase M N g hv ψ) =
      homRebase M N g' hv''
        (homTransport ((modulePullback B S hS p).obj M) ((modulePullback B S hS p).obj N) w hw
          ψ) := by
  subst hw
  have hM := congrArg Iso.hom (pullbackComparison_trans_mapIso w g p hv hv' hv'' M)
  have hN := congrArg Iso.inv (pullbackComparison_trans_mapIso w g p hv hv' hv'' N)
  simp only [Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv] at hM hN
  rw [homTransport_def, homTransport_def, homRebase_def, homRebase_def, homRebase_def,
    homRebase_def]
  exact conj_map_eq_of_comp_eq (modulePullback B S hS w) _ _ _ _ _ _ _ _ ψ hM hN

/-- **Inverse images of morphisms compose.** -/
theorem homTransport_homTransport {P T T' : AlgebraicSpaces B S hS} (w : T' ⟶ T) (g : T ⟶ P)
    {p : P ⟶ A} {v : T ⟶ A} (hv : g ≫ p = v) {v' : T' ⟶ A} (hv' : w ≫ v = v')
    (hv'' : (w ≫ g) ≫ p = v')
    (ψ : (modulePullback B S hS p).obj M ⟶ (modulePullback B S hS p).obj N) :
    homTransport M N w hv' (homTransport M N g hv ψ) = homTransport M N (w ≫ g) hv'' ψ := by
  rw [homTransport_def g hv ψ, homTransport_homRebase w g hv hv' rfl hv'', homTransport_map,
    homTransport_def]

/-- Equality of iterated inverse images of two morphisms is equality of their inverse images
along the composite. -/
theorem map_map_eq_iff {P T : AlgebraicSpaces B S hS} (g : T ⟶ P) (p : P ⟶ A) {v : T ⟶ A}
    (hv : g ≫ p = v) (ψ₁ ψ₂ : M ⟶ N) :
    (modulePullback B S hS g).map ((modulePullback B S hS p).map ψ₁) =
        (modulePullback B S hS g).map ((modulePullback B S hS p).map ψ₂) ↔
      (modulePullback B S hS v).map ψ₁ = (modulePullback B S hS v).map ψ₂ := by
  rw [← homTransport_map g hv ψ₁, ← homTransport_map g hv ψ₂, homTransport_def, homTransport_def]
  exact (homRebase_injective g hv).eq_iff.symm

/-- Inverse images along equal morphisms agree. -/
theorem homTransport_congr {P T : AlgebraicSpaces B S hS} {g g' : T ⟶ P} (h : g = g')
    {p : P ⟶ A} {v : T ⟶ A} (hv : g ≫ p = v) (hv' : g' ≫ p = v)
    (ψ : (modulePullback B S hS p).obj M ⟶ (modulePullback B S hS p).obj N) :
    homTransport M N g hv ψ = homTransport M N g' hv' ψ := by
  subst h
  rfl

/-- The comparisons of Stacks 03LU at a factorization `g ≫ p = v`, as a natural isomorphism
`p^* ⋙ g^* ≅ v^*`. -/
def pullbackComparisonNatIso {P T : AlgebraicSpaces B S hS} (g : T ⟶ P) (p : P ⟶ A)
    (v : T ⟶ A) (hv : g ≫ p = v) :
    modulePullback B S hS p ⋙ modulePullback B S hS g ≅ modulePullback B S hS v :=
  NatIso.ofComponents (fun M => (pullbackComparison B S hS g p v hv M).symm)
    fun χ => pullbackComparison_inv_naturality B S hS g p v hv χ

/-- The component of `pullbackComparisonNatIso` at `M` is the inverse of the comparison
isomorphism `pullbackComparison` at `M`. -/
theorem pullbackComparisonNatIso_hom_app {P T : AlgebraicSpaces B S hS} (g : T ⟶ P)
    (p : P ⟶ A) (v : T ⟶ A) (hv : g ≫ p = v) (M : Modules.{u, u} B S hS A.1 A.2) :
    (pullbackComparisonNatIso g p v hv).hom.app M = (pullbackComparison B S hS g p v hv M).inv :=
  rfl

/-- **Descent along the comparison of Stacks 03LU is being an inverse image.** -/
theorem descendsAlong_pullbackComparisonNatIso_iff {P T : AlgebraicSpaces B S hS} (g : T ⟶ P)
    (p : P ⟶ A) (v : T ⟶ A) (hv : g ≫ p = v)
    (φ : (modulePullback B S hS v).obj M ⟶ (modulePullback B S hS v).obj N) :
    Functor.DescendsAlong (pullbackComparisonNatIso g p v hv) φ ↔
      ∃ ψ : (modulePullback B S hS p).obj M ⟶ (modulePullback B S hS p).obj N,
        homTransport M N g hv ψ = φ := by
  refine exists_congr fun ψ => ?_
  rw [pullbackComparisonNatIso_hom_app, pullbackComparisonNatIso_hom_app, homTransport_def,
    homRebase_def]
  exact Iso.eq_inv_comp _

/-! ### The condition of Stacks 04W5 -/

/-- The canonical comparison at a pair of morphisms with equal composites, through the
comparisons of Stacks 03LU at the common composite. -/
theorem canonicalComparison_hom_eq_pullbackComparison {P Y : AlgebraicSpaces B S hS}
    (a b : P ⟶ Y) (u : Y ⟶ A) (hab : a ≫ u = b ≫ u) (M : Modules.{u, u} B S hS A.1 A.2) :
    (canonicalComparison a b u u hab M).hom =
      (pullbackComparison B S hS a u (a ≫ u) rfl M).inv ≫
        (pullbackComparison B S hS b u (a ≫ u) hab.symm M).hom := by
  rewrite [canonicalComparison_eq, pullbackComparison_hom_eq b u hab.symm M,
    pullbackComparison_rfl, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    eqToIso.hom, Iso.symm_inv, Iso.app_hom]
  exact comp₃_congr rfl rfl rfl

private theorem conj_eq_iff {C : Type*} [Category* C] {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : C} (α : Z₁ ≅ X₁)
    (β : Z₁ ≅ Y₁) (α' : Z₂ ≅ X₂) (β' : Z₂ ≅ Y₂) (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) :
    f ≫ α'.inv ≫ β'.hom = (α.inv ≫ β.hom) ≫ g ↔ α.hom ≫ f ≫ α'.inv = β.hom ≫ g ≫ β'.inv := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← cancel_mono β'.hom, Category.assoc, Category.assoc, h]
    simp
  · rw [← cancel_epi α.hom, reassoc_of% h]
    simp

/-- **The condition of Stacks 04W5 at a pair is the equality of the two inverse images.** -/
theorem map_comp_canonicalComparison_iff {P Y : AlgebraicSpaces B S hS} (a b : P ⟶ Y)
    (u : Y ⟶ A) (hab : a ≫ u = b ≫ u)
    (ψ : (modulePullback B S hS u).obj M ⟶ (modulePullback B S hS u).obj N) :
    (modulePullback B S hS a).map ψ ≫ (canonicalComparison a b u u hab N).hom =
        (canonicalComparison a b u u hab M).hom ≫ (modulePullback B S hS b).map ψ ↔
      homTransport M N a rfl ψ = homTransport M N b hab.symm ψ := by
  rw [canonicalComparison_hom_eq_pullbackComparison, canonicalComparison_hom_eq_pullbackComparison,
    homTransport_def, homTransport_def, homRebase_def, homRebase_def]
  exact conj_eq_iff _ _ _ _ _ _

/-! ### Descent along a surjective étale morphism -/

/-- **The condition at the kernel pair gives the condition at every pair.** -/
theorem homTransport_eq_of_isPullback {R U Y P : AlgebraicSpaces B S hS} {s t : R ⟶ U}
    {u : U ⟶ Y} (hk : IsPullback s.hom t.hom u.hom u.hom) {q : U ⟶ A}
    (ψ : (modulePullback B S hS q).obj M ⟶ (modulePullback B S hS q).obj N) {r : R ⟶ A}
    (hs : s ≫ q = r) (ht : t ≫ q = r) (hst : homTransport M N s hs ψ = homTransport M N t ht ψ)
    (a b : P ⟶ U) (hab : a ≫ u = b ≫ u) (hab' : b ≫ q = a ≫ q) :
    homTransport M N a rfl ψ = homTransport M N b hab' ψ := by
  obtain ⟨h, rfl, rfl⟩ : ∃ h : P ⟶ R, h ≫ s = a ∧ h ≫ t = b :=
    ⟨ObjectProperty.homMk (hk.lift a.hom b.hom (congrArg (fun f => f.hom) hab)),
      ObjectProperty.hom_ext _ (hk.lift_fst _ _ _), ObjectProperty.hom_ext _ (hk.lift_snd _ _ _)⟩
  have h₁ : h ≫ r = (h ≫ s) ≫ q := by rw [← hs, Category.assoc]
  rw [← homTransport_homTransport h s hs h₁ rfl, ← homTransport_homTransport h t ht h₁ hab', hst]

/-- **Descent of morphisms along a surjective étale morphism, from the condition at its kernel
pair** (Stacks 04W6 for the covering `{u}`). A morphism `ψ : q^*M ⟶ q^*N` for `q = u ≫ π`
whose inverse images along the two projections of the kernel pair of `u` agree is the inverse
image along `u` of a morphism `π^*M ⟶ π^*N`. -/
theorem exists_homTransport_eq_of_isPullback {U Y R : AlgebraicSpaces B S hS} (u : U ⟶ Y)
    (hu : IsEtale B S hS u.hom) (hrep : yoneda.relativelyRepresentable u.hom)
    (hcov : IsEtaleCovering B S hS (fun _ : Unit => U.1) (fun _ => u.hom)) {s t : R ⟶ U}
    (hk : IsPullback s.hom t.hom u.hom u.hom) (π : Y ⟶ A) {q : U ⟶ A} (hq : u ≫ π = q)
    (ψ : (modulePullback B S hS q).obj M ⟶ (modulePullback B S hS q).obj N)
    {r : R ⟶ A} (hs : s ≫ q = r) (ht : t ≫ q = r)
    (hst : homTransport M N s hs ψ = homTransport M N t ht ψ) :
    ∃ χ : (modulePullback B S hS π).obj M ⟶ (modulePullback B S hS π).obj N,
      homTransport M N u hq χ = ψ := by
  let ψ₀ := (pullbackComparison B S hS u π q hq M).inv ≫ ψ ≫
    (pullbackComparison B S hS u π q hq N).hom
  have hψ₀ : homRebase M N u hq ψ₀ = ψ := by
    rw [homRebase_def]
    simp [ψ₀]
  obtain ⟨χ, hχ⟩ := exists_modulePullback_map_eq_of_dominated B S hS u hu hrep hcov ψ₀
    fun P a b hab => by
      rw [map_comp_canonicalComparison_iff]
      apply homRebase_injective (a ≫ u) (v := a ≫ q) (by rw [Category.assoc, hq])
      rw [← homTransport_homRebase a u hq rfl rfl, ← homTransport_homRebase b u hq
        (by rw [← hq, ← Category.assoc, ← hab, Category.assoc]) hab.symm, hψ₀]
      exact homTransport_eq_of_isPullback hk ψ hs ht hst a b hab _
  exact ⟨χ, by rw [homTransport_def, hχ, hψ₀]⟩

/-- **A morphism is determined by its inverse image along an étale covering**, in the form of
inverse images of morphisms of inverse images. -/
theorem homTransport_injective {U Y : AlgebraicSpaces B S hS} (u : U ⟶ Y)
    (hcov : IsEtaleCovering B S hS (fun _ : Unit => U.1) (fun _ => u.hom)) {π : Y ⟶ A}
    {q : U ⟶ A} (hq : u ≫ π = q) : Function.Injective (homTransport M N u hq) := by
  intro χ₁ χ₂ h
  rw [homTransport_def, homTransport_def] at h
  exact modulePullback_map_injective_of_isEtaleCovering B S hS (fun _ : Unit => U) (fun _ => u)
    hcov χ₁ χ₂ fun _ => homRebase_injective u hq h

end AlgebraicGeometry.Space.QuasiCoherentDescent

end
