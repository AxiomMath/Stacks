module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.Canonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.SingleMorphismHomDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardCompIsoAssoc

/-!
# Restricting morphisms of inverse images along morphisms over a base

Let `Z` be an algebraic space and `M`, `N` two `𝒪_Z`-modules.  For an algebraic space `P` with a
morphism `p : P ⟶ Z`, a morphism `p^*M ⟶ p^*N` can be restricted along any `g : Q ⟶ P` to a
morphism `q^*M ⟶ q^*N`, where `q = g ≫ p`, through the comparisons of iterated inverse images of
Stacks 03LU.  This file records that restriction and its calculus: it is functorial in `g`, it
carries the inverse image of a morphism `M ⟶ N` to the inverse image of that morphism, it is
injective along a surjective étale morphism, and a morphism over `Q` descends along a surjective
étale relatively representable `g` as soon as its two restrictions to every pair of morphisms
into `Q` with equal composites to `P` agree.

## Main definitions

* `AlgebraicGeometry.Space.moduleHomRestrict`: the restriction.

## Main results

* `AlgebraicGeometry.Space.moduleHomRestrict_homRestrict`: functoriality.
* `AlgebraicGeometry.Space.moduleHomRestrict_map`: restriction of an inverse image.
* `AlgebraicGeometry.Space.moduleHomRestrict_injective`: injectivity along a morphism with
  faithful inverse image.
* `AlgebraicGeometry.Space.exists_homRestrict_eq_of_descent`: descent along a surjective étale
  relatively representable morphism.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 04W6](https://stacks.math.columbia.edu/tag/04W6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

open QuasiCoherentDescent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {Z : AlgebraicSpaces B S hS} (M N : Modules.{u, u} B S hS Z.1 Z.2)

/-- The restriction of a morphism `p^*M ⟶ p^*N` along `g : Q ⟶ P`, as a morphism
`q^*M ⟶ q^*N` for `q = g ≫ p`. -/
noncomputable def moduleHomRestrict {P Q : AlgebraicSpaces B S hS} (g : Q ⟶ P) (p : P ⟶ Z)
    (q : Q ⟶ Z) (h : g ≫ p = q)
    (x : (modulePullback B S hS p).obj M ⟶ (modulePullback B S hS p).obj N) :
    (modulePullback B S hS q).obj M ⟶ (modulePullback B S hS q).obj N :=
  (pullbackComparison B S hS g p q h M).hom ≫ (modulePullback B S hS g).map x ≫
    (pullbackComparison B S hS g p q h N).inv

variable {M N}

/-- At the composite itself the restriction is conjugation by the comparison of Stacks 03LU. -/
theorem moduleHomRestrict_rfl {P Q : AlgebraicSpaces B S hS} (g : Q ⟶ P) (p : P ⟶ Z)
    (x : (modulePullback B S hS p).obj M ⟶ (modulePullback B S hS p).obj N) :
    moduleHomRestrict M N g p (g ≫ p) rfl x =
      (modulePullbackCompIso B S hS g p).inv.app M ≫ (modulePullback B S hS g).map x ≫
        (modulePullbackCompIso B S hS g p).hom.app N := by
  simp only [moduleHomRestrict, pullbackComparison_rfl]
  rfl

/-- **Restriction is functorial.** -/
theorem moduleHomRestrict_homRestrict {P Q R : AlgebraicSpaces B S hS} (g : Q ⟶ P) (g' : R ⟶ Q)
    (p : P ⟶ Z) (q : Q ⟶ Z) (r : R ⟶ Z) (h : g ≫ p = q) (h' : g' ≫ q = r)
    (x : (modulePullback B S hS p).obj M ⟶ (modulePullback B S hS p).obj N) :
    moduleHomRestrict M N g' q r h' (moduleHomRestrict M N g p q h x) =
      moduleHomRestrict M N (g' ≫ g) p r (by rw [Category.assoc, h, h']) x := by
  subst h h'
  rw [moduleHomRestrict_rfl, moduleHomRestrict_rfl]
  change _ = moduleHomRestrict M N (g' ≫ g) p ((g' ≫ g) ≫ p) rfl x
  rw [moduleHomRestrict_rfl]
  have hM := (modulePullbackCompIsoAssoc B S hS).inv_app g' g p M
  have hN := (modulePullbackCompIsoAssoc B S hS).hom_app g' g p N
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hM, hN]
  have hnat := (modulePullbackCompIso B S hS g' g).hom.naturality x
  simp only [Functor.comp_map] at hnat
  rw [reassoc_of% hnat, Iso.inv_hom_id_app_assoc]

/-- **Restriction of an inverse image is the inverse image.** -/
theorem moduleHomRestrict_map {P Q : AlgebraicSpaces B S hS} (g : Q ⟶ P) (p : P ⟶ Z) (q : Q ⟶ Z)
    (h : g ≫ p = q) (χ : M ⟶ N) :
    moduleHomRestrict M N g p q h ((modulePullback B S hS p).map χ) =
      (modulePullback B S hS q).map χ := by
  subst h
  rw [moduleHomRestrict_rfl]
  have := (modulePullbackCompIso B S hS g p).hom.naturality χ
  simp only [Functor.comp_map] at this
  rw [this, Iso.inv_hom_id_app_assoc]

/-- The comparison of an inverse image with an iterated inverse image is natural in the
module. -/
theorem pullbackComparison_hom_naturality {P Q : AlgebraicSpaces B S hS} (g : Q ⟶ P)
    (p : P ⟶ Z) (q : Q ⟶ Z) (h : g ≫ p = q) (f : M ⟶ N) :
    (pullbackComparison B S hS g p q h M).hom ≫
        (modulePullback B S hS g).map ((modulePullback B S hS p).map f) =
      (modulePullback B S hS q).map f ≫ (pullbackComparison B S hS g p q h N).hom := by
  subst h
  rw [pullbackComparison_rfl, pullbackComparison_rfl]
  exact ((modulePullbackCompIso B S hS g p).inv.naturality f).symm

/-- Restriction is conjugation by the comparison of Stacks 03LU followed by the transport along
the equality of the composite. -/
theorem moduleHomRestrict_eq_compIso {P Q : AlgebraicSpaces B S hS} (g : Q ⟶ P) (p : P ⟶ Z)
    (q : Q ⟶ Z) (h : g ≫ p = q)
    (x : (modulePullback B S hS p).obj M ⟶ (modulePullback B S hS p).obj N) :
    moduleHomRestrict M N g p q h x =
      (modulePullbackCompIso B S hS g p ≪≫ eqToIso (congrArg (modulePullback B S hS) h)).inv.app
          M ≫ (modulePullback B S hS g).map x ≫
        (modulePullbackCompIso B S hS g p ≪≫ eqToIso (congrArg (modulePullback B S hS) h)).hom.app
          N := by
  subst h
  rw [moduleHomRestrict_rfl]
  simp

/-- **Restriction is compatible with composition of morphisms.** -/
theorem moduleHomRestrict_comp {K : Modules.{u, u} B S hS Z.1 Z.2} {P Q : AlgebraicSpaces B S hS}
    (g : Q ⟶ P) (p : P ⟶ Z) (q : Q ⟶ Z) (h : g ≫ p = q)
    (x : (modulePullback B S hS p).obj M ⟶ (modulePullback B S hS p).obj N)
    (y : (modulePullback B S hS p).obj N ⟶ (modulePullback B S hS p).obj K) :
    moduleHomRestrict M K g p q h (x ≫ y) =
      moduleHomRestrict M N g p q h x ≫ moduleHomRestrict N K g p q h y := by
  simp [moduleHomRestrict]

/-- Restriction of a morphism conjugated by inverse images of morphisms of the base modules. -/
theorem moduleHomRestrict_map_comp_comp {M' N' : Modules.{u, u} B S hS Z.1 Z.2}
    {P Q : AlgebraicSpaces B S hS} (g : Q ⟶ P) (p : P ⟶ Z) (q : Q ⟶ Z) (h : g ≫ p = q)
    (a : M ⟶ M') (b : N' ⟶ N)
    (x : (modulePullback B S hS p).obj M' ⟶ (modulePullback B S hS p).obj N') :
    moduleHomRestrict M N g p q h ((modulePullback B S hS p).map a ≫ x ≫
        (modulePullback B S hS p).map b) =
      (modulePullback B S hS q).map a ≫ moduleHomRestrict M' N' g p q h x ≫
        (modulePullback B S hS q).map b := by
  rw [moduleHomRestrict_comp, moduleHomRestrict_comp, moduleHomRestrict_map, moduleHomRestrict_map]

/-- Two restrictions agree exactly when the two inverse images agree. -/
theorem moduleHomRestrict_eq_iff {P Q : AlgebraicSpaces B S hS} (g : Q ⟶ P) (p : P ⟶ Z) (q : Q ⟶ Z)
    (h : g ≫ p = q)
    (x y : (modulePullback B S hS p).obj M ⟶ (modulePullback B S hS p).obj N) :
    moduleHomRestrict M N g p q h x = moduleHomRestrict M N g p q h y ↔
      (modulePullback B S hS g).map x = (modulePullback B S hS g).map y := by
  unfold moduleHomRestrict
  rw [Iso.cancel_iso_hom_left, Iso.cancel_iso_inv_right]

/-- Restriction depends on the morphism along which it is taken only through its value. -/
theorem moduleHomRestrict_congr {P Q : AlgebraicSpaces B S hS} {g g' : Q ⟶ P} (e : g = g')
    (p : P ⟶ Z) (q : Q ⟶ Z) (h : g ≫ p = q)
    (x : (modulePullback B S hS p).obj M ⟶ (modulePullback B S hS p).obj N) :
    moduleHomRestrict M N g p q h x = moduleHomRestrict M N g' p q (e ▸ h) x := by
  subst e
  rfl

/-- **Restriction along a morphism with faithful inverse image is injective.** -/
theorem moduleHomRestrict_injective {P Q : AlgebraicSpaces B S hS} (g : Q ⟶ P) (p : P ⟶ Z)
    (q : Q ⟶ Z) (h : g ≫ p = q) [(modulePullback B S hS g).Faithful]
    {x y : (modulePullback B S hS p).obj M ⟶ (modulePullback B S hS p).obj N}
    (hxy : moduleHomRestrict M N g p q h x = moduleHomRestrict M N g p q h y) : x = y := by
  apply (modulePullback B S hS g).map_injective
  simpa [moduleHomRestrict] using hxy

/-- Restriction to a target given up to an equality is restriction to the composite followed by
transport along that equality. -/
theorem moduleHomRestrict_eq_eqToHom {P Q : AlgebraicSpaces B S hS} (g : Q ⟶ P) (p : P ⟶ Z)
    (q : Q ⟶ Z) (h : g ≫ p = q)
    (x : (modulePullback B S hS p).obj M ⟶ (modulePullback B S hS p).obj N) :
    moduleHomRestrict M N g p q h x =
      eqToHom (congrArg (fun t : Q ⟶ Z => (modulePullback B S hS t).obj M) h.symm) ≫
        moduleHomRestrict M N g p (g ≫ p) rfl x ≫
        eqToHom (congrArg (fun t : Q ⟶ Z => (modulePullback B S hS t).obj N) h) := by
  subst h
  simp

/-- Conjugating a morphism by two pairs of isomorphisms with common targets. -/
private theorem comp_trans_symm_iff {C : Type*} [Category C] {A A' B B' Y Y' : C}
    (ya : A ⟶ A') (yb : B ⟶ B') (α : A ≅ Y) (α' : A' ≅ Y') (β : B ≅ Y) (β' : B' ≅ Y') :
    ya ≫ (α' ≪≫ β'.symm).hom = (α ≪≫ β.symm).hom ≫ yb ↔
      α.inv ≫ ya ≫ α'.hom = β.inv ≫ yb ≫ β'.hom := by
  simp only [Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, Iso.comp_inv_eq, Iso.inv_comp_eq]
  simp only [Category.assoc]

/-- The comparison of an inverse image along a morphism given up to an equality is the transport
along that equality followed by the comparison at the composite. -/
theorem pullbackComparison_eq_trans {A P T : AlgebraicSpaces B S hS} (g : T ⟶ P) (p : P ⟶ A)
    (v : T ⟶ A) (hv : g ≫ p = v) (M : Modules.{u, u} B S hS A.1 A.2) :
    pullbackComparison B S hS g p v hv M =
      eqToIso (congrArg (fun q : T ⟶ A => (modulePullback B S hS q).obj M) hv.symm) ≪≫
        pullbackComparison B S hS g p (g ≫ p) rfl M := by
  subst hv
  exact (Iso.refl_trans _).symm

/-- **The descent condition of Stacks 04W3 for one morphism, read through restriction.**  A
morphism `y : g^*M ⟶ g^*N` is intertwined by the canonical comparison of Stacks 04W5 at a pair
`a, b` with `a ≫ g = b ≫ g` exactly when its two restrictions along `a` and `b` agree. -/
theorem map_comp_canonicalComparison_iff {P Q T : AlgebraicSpaces B S hS} (g : Q ⟶ P)
    {M N : Modules.{u, u} B S hS P.1 P.2}
    (y : (modulePullback B S hS g).obj M ⟶ (modulePullback B S hS g).obj N)
    (a b : T ⟶ Q) (hab : a ≫ g = b ≫ g) :
    (modulePullback B S hS a).map y ≫ (canonicalComparison a b g g hab N).hom =
        (canonicalComparison a b g g hab M).hom ≫ (modulePullback B S hS b).map y ↔
      moduleHomRestrict M N a g (a ≫ g) rfl y = moduleHomRestrict M N b g (a ≫ g) hab.symm y := by
  have hc : ∀ X : Modules.{u, u} B S hS P.1 P.2, canonicalComparison a b g g hab X =
      (pullbackComparison B S hS a g (a ≫ g) rfl X).symm ≪≫
        (pullbackComparison B S hS b g (a ≫ g) hab.symm X).symm.symm := fun X => by
    rw [Iso.symm_symm_eq, pullbackComparison_eq_trans b g (a ≫ g) hab.symm X,
      canonicalComparison]
  rw [hc M, hc N]
  exact comp_trans_symm_iff _ _ _ _ _ _

variable (B S hS) in
/-- **Descent of a morphism of inverse images along a surjective étale relatively representable
morphism.**  A morphism `y : g^*M ⟶ g^*N` whose two restrictions to every pair of morphisms
into `Q` with equal composites to `P` agree is the inverse image of a morphism `M ⟶ N`. -/
theorem exists_modulePullback_map_eq_of_homRestrict {P Q : AlgebraicSpaces B S hS} (g : Q ⟶ P)
    (hg : IsEtale B S hS g.hom) (hrep : yoneda.relativelyRepresentable g.hom)
    (hcov : IsEtaleCovering B S hS (fun _ : Unit => Q.1) (fun _ => g.hom))
    {M N : Modules.{u, u} B S hS P.1 P.2}
    (y : (modulePullback B S hS g).obj M ⟶ (modulePullback B S hS g).obj N)
    (hy : ∀ (T : AlgebraicSpaces B S hS) (a b : T ⟶ Q) (hab : a ≫ g = b ≫ g),
      moduleHomRestrict M N a g (a ≫ g) rfl y = moduleHomRestrict M N b g (a ≫ g) hab.symm y) :
    ∃ x : M ⟶ N, (modulePullback B S hS g).map x = y :=
  exists_modulePullback_map_eq_of_dominated B S hS g hg hrep hcov y
    fun T a b hab => (map_comp_canonicalComparison_iff g y a b hab).2 (hy T a b hab)

/-- Restrictions to two morphisms factoring through a pair with equal restrictions agree. -/
private theorem moduleHomRestrict_eq_of_factor_aux {Q R T : AlgebraicSpaces B S hS} (q : Q ⟶ Z)
    (y : (modulePullback B S hS q).obj M ⟶ (modulePullback B S hS q).obj N)
    (P₁ P₂ : R ⟶ Q) (tg : R ⟶ Z) (h₁ : P₁ ≫ q = tg) (h₂ : P₂ ≫ q = tg)
    (hK : moduleHomRestrict M N P₁ q tg h₁ y = moduleHomRestrict M N P₂ q tg h₂ y)
    (v : T ⟶ R) (a b : T ⟶ Q) (hva : v ≫ P₁ = a) (hvb : v ≫ P₂ = b) (t' : T ⟶ Z)
    (ha : a ≫ q = t') (hb : b ≫ q = t') :
    moduleHomRestrict M N a q t' ha y = moduleHomRestrict M N b q t' hb y := by
  subst hva hvb
  have e1 := moduleHomRestrict_homRestrict P₁ v q tg t' h₁ (by rw [← h₁, ← Category.assoc, ha]) y
  have e2 := moduleHomRestrict_homRestrict P₂ v q tg t' h₂ (by rw [← h₂, ← Category.assoc, hb]) y
  rw [← e1, ← e2, hK]

/-- **The descent condition need only be checked at the kernel pair.**  If the two
restrictions of `y` to the two projections of `Q ×_P Q` agree, then its two restrictions to any
pair of morphisms into `Q` with equal composites to `P` agree. -/
theorem moduleHomRestrict_eq_of_isPullback {P Q R : AlgebraicSpaces B S hS} (g : Q ⟶ P)
    (pr₁ pr₂ : R ⟶ Q) (hpb : IsPullback pr₁.hom pr₂.hom g.hom g.hom)
    {M N : Modules.{u, u} B S hS P.1 P.2}
    (y : (modulePullback B S hS g).obj M ⟶ (modulePullback B S hS g).obj N)
    (hy : moduleHomRestrict M N pr₁ g (pr₁ ≫ g) rfl y =
      moduleHomRestrict M N pr₂ g (pr₁ ≫ g) (ObjectProperty.hom_ext _ hpb.w).symm y)
    (T : AlgebraicSpaces B S hS) (a b : T ⟶ Q) (hab : a ≫ g = b ≫ g) :
    moduleHomRestrict M N a g (a ≫ g) rfl y = moduleHomRestrict M N b g (a ≫ g) hab.symm y := by
  refine moduleHomRestrict_eq_of_factor_aux g y pr₁ pr₂ (pr₁ ≫ g) rfl
    (ObjectProperty.hom_ext _ hpb.w).symm hy
    (ObjectProperty.homMk (hpb.lift a.hom b.hom (congrArg (fun t => t.hom) hab))) a b
    (ObjectProperty.hom_ext _ (hpb.lift_fst _ _ _))
    (ObjectProperty.hom_ext _ (hpb.lift_snd _ _ _)) _ rfl hab.symm

/-- **The descent condition need only be checked at one pair through which every pair
factors.** -/
theorem moduleHomRestrict_eq_of_forall_factor {P Q R : AlgebraicSpaces B S hS} (g : Q ⟶ P)
    (pr₁ pr₂ : R ⟶ Q) (hw : pr₁ ≫ g = pr₂ ≫ g)
    (hf : ∀ (T : AlgebraicSpaces B S hS) (a b : T ⟶ Q), a ≫ g = b ≫ g →
      ∃ v : T ⟶ R, v ≫ pr₁ = a ∧ v ≫ pr₂ = b)
    {M N : Modules.{u, u} B S hS P.1 P.2}
    (y : (modulePullback B S hS g).obj M ⟶ (modulePullback B S hS g).obj N)
    (hy : moduleHomRestrict M N pr₁ g (pr₁ ≫ g) rfl y =
      moduleHomRestrict M N pr₂ g (pr₁ ≫ g) hw.symm y)
    (T : AlgebraicSpaces B S hS) (a b : T ⟶ Q) (hab : a ≫ g = b ≫ g) :
    moduleHomRestrict M N a g (a ≫ g) rfl y = moduleHomRestrict M N b g (a ≫ g) hab.symm y := by
  obtain ⟨v, hva, hvb⟩ := hf T a b hab
  exact moduleHomRestrict_eq_of_factor_aux g y pr₁ pr₂ (pr₁ ≫ g) rfl hw.symm hy v a b hva hvb _
    rfl hab.symm

/-- Conjugation of a morphism between iterated inverse images along `r` and `f` into a morphism
between the inverse images along `r ≫ f`. -/
noncomputable def homConj {V P : AlgebraicSpaces B S hS} (f : V ⟶ Z) (r : P ⟶ V)
    (x : (modulePullback B S hS r).obj ((modulePullback B S hS f).obj M) ⟶
      (modulePullback B S hS r).obj ((modulePullback B S hS f).obj N)) :
    (modulePullback B S hS (r ≫ f)).obj M ⟶ (modulePullback B S hS (r ≫ f)).obj N :=
  (modulePullbackCompIso B S hS r f).inv.app M ≫ x ≫ (modulePullbackCompIso B S hS r f).hom.app N

/-- The inverse of `homConj`. -/
noncomputable def homConjInv {V P : AlgebraicSpaces B S hS} (f : V ⟶ Z) (r : P ⟶ V)
    (y : (modulePullback B S hS (r ≫ f)).obj M ⟶ (modulePullback B S hS (r ≫ f)).obj N) :
    (modulePullback B S hS r).obj ((modulePullback B S hS f).obj M) ⟶
      (modulePullback B S hS r).obj ((modulePullback B S hS f).obj N) :=
  (modulePullbackCompIso B S hS r f).hom.app M ≫ y ≫ (modulePullbackCompIso B S hS r f).inv.app N

/-- `homConj` is a left inverse of `homConjInv`. -/
theorem homConj_homConjInv {V P : AlgebraicSpaces B S hS} (f : V ⟶ Z) (r : P ⟶ V)
    (y : (modulePullback B S hS (r ≫ f)).obj M ⟶ (modulePullback B S hS (r ≫ f)).obj N) :
    homConj f r (homConjInv f r y) = y := by
  simp [homConj, homConjInv]

/-- `homConjInv` is a left inverse of `homConj`. -/
theorem homConjInv_homConj {V P : AlgebraicSpaces B S hS} (f : V ⟶ Z) (r : P ⟶ V)
    (x : (modulePullback B S hS r).obj ((modulePullback B S hS f).obj M) ⟶
      (modulePullback B S hS r).obj ((modulePullback B S hS f).obj N)) :
    homConjInv f r (homConj f r x) = x := by
  simp [homConj, homConjInv]

/-- `homConj` is injective. -/
theorem homConj_injective {V P : AlgebraicSpaces B S hS} (f : V ⟶ Z) (r : P ⟶ V)
    {x x' : (modulePullback B S hS r).obj ((modulePullback B S hS f).obj M) ⟶
      (modulePullback B S hS r).obj ((modulePullback B S hS f).obj N)}
    (h : homConj f r x = homConj f r x') : x = x' := by
  rw [← homConjInv_homConj f r x, h, homConjInv_homConj]

/-- Restriction along `r` of a morphism over `p`, as `homConj` of its inverse image. -/
theorem moduleHomRestrict_eq_homConj {P Q : AlgebraicSpaces B S hS} (g : Q ⟶ P) (p : P ⟶ Z)
    (x : (modulePullback B S hS p).obj M ⟶ (modulePullback B S hS p).obj N) :
    moduleHomRestrict M N g p (g ≫ p) rfl x = homConj p g ((modulePullback B S hS g).map x) := by
  rw [moduleHomRestrict_rfl]
  rfl

/-- **Restriction commutes with `homConj`.** -/
theorem homConj_homRestrict {V P Q : AlgebraicSpaces B S hS} (f : V ⟶ Z) (r : P ⟶ V)
    (s : Q ⟶ P)
    (x : (modulePullback B S hS r).obj ((modulePullback B S hS f).obj M) ⟶
      (modulePullback B S hS r).obj ((modulePullback B S hS f).obj N)) :
    homConj f (s ≫ r) (moduleHomRestrict ((modulePullback B S hS f).obj M)
        ((modulePullback B S hS f).obj N) s r (s ≫ r) rfl x) =
      moduleHomRestrict M N s (r ≫ f) ((s ≫ r) ≫ f) (Category.assoc _ _ _).symm
        (homConj f r x) := by
  rw [moduleHomRestrict_rfl]
  change _ = moduleHomRestrict M N s (r ≫ f) (s ≫ r ≫ f) rfl (homConj f r x)
  rw [moduleHomRestrict_rfl]
  have hM := (modulePullbackCompIsoAssoc B S hS).inv_app s r f M
  have hN := (modulePullbackCompIsoAssoc B S hS).hom_app s r f N
  simp only [homConj, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hM, hN]

/-- **Restriction commutes with `homConj`**, with the target of the inner restriction given up to
an equality. -/
theorem homConj_homRestrict' {V P Q : AlgebraicSpaces B S hS} (f : V ⟶ Z) (r : P ⟶ V)
    (s : Q ⟶ P) (q : Q ⟶ V) (hq : s ≫ r = q)
    (x : (modulePullback B S hS r).obj ((modulePullback B S hS f).obj M) ⟶
      (modulePullback B S hS r).obj ((modulePullback B S hS f).obj N)) :
    homConj f q (moduleHomRestrict ((modulePullback B S hS f).obj M)
        ((modulePullback B S hS f).obj N) s r q hq x) =
      moduleHomRestrict M N s (r ≫ f) (q ≫ f) (by rw [← hq, Category.assoc]) (homConj f r x) := by
  subst hq
  exact homConj_homRestrict f r s x

/-- **Changing the base of a restriction.**  A morphism over `t` with modules pulled back along
`f` whose restriction along `s` is (the conjugate of) a given `χ` yields a morphism over any
`wl = t ≫ f` with modules on the base of `f` whose restriction along `s` is `χ`. -/
theorem exists_homRestrict_eq_of_homRestrict_eq_homConjInv {V P Q : AlgebraicSpaces B S hS}
    (f : V ⟶ Z) (t : P ⟶ V) (s : Q ⟶ P) (π : Q ⟶ V) (hπ : s ≫ t = π) (wl : P ⟶ Z)
    (hwl : t ≫ f = wl)
    (ψ' : (modulePullback B S hS t).obj ((modulePullback B S hS f).obj M) ⟶
      (modulePullback B S hS t).obj ((modulePullback B S hS f).obj N))
    (χ : (modulePullback B S hS (π ≫ f)).obj M ⟶ (modulePullback B S hS (π ≫ f)).obj N)
    (h : moduleHomRestrict ((modulePullback B S hS f).obj M) ((modulePullback B S hS f).obj N)
      s t π hπ ψ' = homConjInv f π χ) :
    ∃ ψ : (modulePullback B S hS wl).obj M ⟶ (modulePullback B S hS wl).obj N,
      moduleHomRestrict M N s wl (π ≫ f) (by rw [← hwl, ← hπ, Category.assoc]) ψ = χ := by
  subst hwl
  refine ⟨homConj f t ψ', (homConj_homRestrict' f t s π hπ ψ').symm.trans ?_⟩
  rw [h, homConj_homConjInv]

/-- Equality of inverse images of conjugates is equality of restrictions. -/
theorem map_homConjInv_eq_iff {V P Q : AlgebraicSpaces B S hS} (f : V ⟶ Z) (r : P ⟶ V)
    (g : Q ⟶ P)
    (y₁ y₂ : (modulePullback B S hS (r ≫ f)).obj M ⟶ (modulePullback B S hS (r ≫ f)).obj N) :
    (modulePullback B S hS g).map (homConjInv f r y₁) =
        (modulePullback B S hS g).map (homConjInv f r y₂) ↔
      moduleHomRestrict M N g (r ≫ f) ((g ≫ r) ≫ f) (Category.assoc _ _ _).symm y₁ =
        moduleHomRestrict M N g (r ≫ f) ((g ≫ r) ≫ f) (Category.assoc _ _ _).symm y₂ := by
  rw [← moduleHomRestrict_eq_iff g r (g ≫ r) rfl]
  constructor
  · intro h
    have e1 := homConj_homRestrict f r g (M := M) (N := N) (homConjInv f r y₁)
    have e2 := homConj_homRestrict f r g (M := M) (N := N) (homConjInv f r y₂)
    rw [homConj_homConjInv] at e1 e2
    rw [← e1, ← e2, h]
  · intro h
    apply homConj_injective f (g ≫ r)
    rwa [homConj_homRestrict, homConj_homRestrict, homConj_homConjInv, homConj_homConjInv]

/-- Restriction along a composite whose second factor is given up to an equality. -/
theorem moduleHomRestrict_homRestrict' {P Q R : AlgebraicSpaces B S hS} (g : Q ⟶ P) (g' : R ⟶ Q)
    (k : R ⟶ P) (hk : g' ≫ g = k) (p : P ⟶ Z) (q : Q ⟶ Z) (r : R ⟶ Z) (h : g ≫ p = q)
    (h' : g' ≫ q = r)
    (x : (modulePullback B S hS p).obj M ⟶ (modulePullback B S hS p).obj N) :
    moduleHomRestrict M N g' q r h' (moduleHomRestrict M N g p q h x) =
      moduleHomRestrict M N k p r (by rw [← hk, Category.assoc, h, h']) x := by
  subst hk
  exact moduleHomRestrict_homRestrict g g' p q r h h' x

variable (B S hS) in
/-- **Descent of a morphism of inverse images along a surjective étale relatively representable
morphism, over an arbitrary base.** -/
theorem exists_homRestrict_eq_of_descent {P Q : AlgebraicSpaces B S hS} (g : Q ⟶ P)
    (hg : IsEtale B S hS g.hom) (hrep : yoneda.relativelyRepresentable g.hom)
    (hcov : IsEtaleCovering B S hS (fun _ : Unit => Q.1) (fun _ => g.hom)) (p : P ⟶ Z)
    (y : (modulePullback B S hS (g ≫ p)).obj M ⟶ (modulePullback B S hS (g ≫ p)).obj N)
    (hy : ∀ (T : AlgebraicSpaces B S hS) (a b : T ⟶ Q) (hab : a ≫ g = b ≫ g),
      moduleHomRestrict M N a (g ≫ p) ((a ≫ g) ≫ p) (Category.assoc _ _ _).symm y =
        moduleHomRestrict M N b (g ≫ p) ((a ≫ g) ≫ p)
          (by rw [← Category.assoc, hab]) y) :
    ∃ x : (modulePullback B S hS p).obj M ⟶ (modulePullback B S hS p).obj N,
      moduleHomRestrict M N g p (g ≫ p) rfl x = y := by
  obtain ⟨x, hx⟩ := exists_modulePullback_map_eq_of_homRestrict B S hS g hg hrep hcov
    (homConjInv p g y) (fun T a b hab => by
      apply homConj_injective p (a ≫ g)
      rw [homConj_homRestrict p g a, homConj_homRestrict' p g b (a ≫ g) hab.symm,
        homConj_homConjInv]
      exact hy T a b hab)
  exact ⟨x, by rw [moduleHomRestrict_eq_homConj, hx, homConj_homConjInv]⟩

/-- **Restrictions to two morphisms factoring through a pair with equal restrictions agree.** -/
theorem moduleHomRestrict_eq_of_factor {Q R T : AlgebraicSpaces B S hS} (q : Q ⟶ Z)
    (y : (modulePullback B S hS q).obj M ⟶ (modulePullback B S hS q).obj N)
    (P₁ P₂ : R ⟶ Q) (tg : R ⟶ Z) (h₁ : P₁ ≫ q = tg) (h₂ : P₂ ≫ q = tg)
    (hK : moduleHomRestrict M N P₁ q tg h₁ y = moduleHomRestrict M N P₂ q tg h₂ y)
    (v : T ⟶ R) (a b : T ⟶ Q) (hva : v ≫ P₁ = a) (hvb : v ≫ P₂ = b) (t' : T ⟶ Z)
    (ha : a ≫ q = t') (hb : b ≫ q = t') :
    moduleHomRestrict M N a q t' ha y = moduleHomRestrict M N b q t' hb y :=
  moduleHomRestrict_eq_of_factor_aux q y P₁ P₂ tg h₁ h₂ hK v a b hva hvb t' ha hb

/-- **Restriction through a factorization.**  If `ψ` restricts along `s` to the restriction `χ`
of `y` along `ell`, then restricting `ψ` along `μ ≫ s` is restricting `y` along `μ ≫ ell`. -/
theorem moduleHomRestrict_eq_of_factor_through {P Q L T : AlgebraicSpaces B S hS} (p : P ⟶ Z)
    (y : (modulePullback B S hS p).obj M ⟶ (modulePullback B S hS p).obj N)
    (ell : L ⟶ P) (v : L ⟶ Z) (hv : ell ≫ p = v) (cl : Q ⟶ Z) (s : L ⟶ Q) (hs : s ≫ cl = v)
    (ψ : (modulePullback B S hS cl).obj M ⟶ (modulePullback B S hS cl).obj N)
    (hψ : moduleHomRestrict M N s cl v hs ψ = moduleHomRestrict M N ell p v hv y)
    (μ : T ⟶ L) (k : T ⟶ Q) (hk : μ ≫ s = k) (F : T ⟶ P) (hF : μ ≫ ell = F) (tg : T ⟶ Z)
    (h₁ : k ≫ cl = tg) (h₂ : F ≫ p = tg) :
    moduleHomRestrict M N k cl tg h₁ ψ = moduleHomRestrict M N F p tg h₂ y := by
  subst hk hF
  have e1 := moduleHomRestrict_homRestrict s μ cl v tg hs (by rw [← hs, ← Category.assoc, h₁]) ψ
  have e2 := moduleHomRestrict_homRestrict ell μ p v tg hv (by rw [← hv, ← Category.assoc, h₂]) y
  rw [← e1, ← e2, hψ]

end AlgebraicGeometry.Space

end
