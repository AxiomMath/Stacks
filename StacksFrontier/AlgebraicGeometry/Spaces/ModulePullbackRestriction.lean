module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardIdIso
public import StacksFrontier.CategoryTheory.Functor.ConjugateHom

/-!
# Restricting homomorphisms between inverse images of modules

For modules `M` on `A` and `N` on `B'` and morphisms `a : Z ⟶ A`, `b : Z ⟶ B'` of algebraic
spaces, a homomorphism `a^*M ⟶ b^*N` restricts along any `φ : Z' ⟶ Z`, read through the
comparisons of Stacks 03LU.  Restriction composes, by the associativity coherence of those
comparisons.  This is the calculus in which the isomorphism sheaves of the stack of coherent
sheaves are compared with the relative Isom functors.

## Main definitions

* `CategoryTheory.Functor.secMap`: restriction of a morphism `Pa M ⟶ Pb N` along a functor,
  read through two comparisons.
* `AlgebraicGeometry.Space.secRestrict`: its instance at the inverse images of modules.

## Main results

* `AlgebraicGeometry.Space.modulePullbackTriangle_comp_app`: the associativity coherence of the
  comparisons of inverse images, read at a module.
* `AlgebraicGeometry.Space.secRestrict_secRestrict`: restriction composes.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits


namespace CategoryTheory.Functor

variable {𝒜 ℬ 𝒵 𝒵' 𝒵'' : Type*} [Category* 𝒜] [Category* ℬ] [Category* 𝒵] [Category* 𝒵']
  [Category* 𝒵'']

/-- The restriction of a morphism `Pa M ⟶ Pb N` along `Φ`, read through comparisons
`Pa' ≅ Pa ⋙ Φ` and `Pb' ≅ Pb ⋙ Φ`. -/
def secMap {Pa : 𝒜 ⥤ 𝒵} {Pb : ℬ ⥤ 𝒵} {Φ : 𝒵 ⥤ 𝒵'} {Pa' : 𝒜 ⥤ 𝒵'} {Pb' : ℬ ⥤ 𝒵'}
    (ta : Pa' ≅ Pa ⋙ Φ) (tb : Pb' ≅ Pb ⋙ Φ) {M : 𝒜} {N : ℬ} (u : Pa.obj M ⟶ Pb.obj N) :
    Pa'.obj M ⟶ Pb'.obj N :=
  ta.hom.app M ≫ Φ.map u ≫ tb.inv.app N

/-- Restriction of an isomorphism is an isomorphism. -/
instance isIso_secMap {Pa : 𝒜 ⥤ 𝒵} {Pb : ℬ ⥤ 𝒵} {Φ : 𝒵 ⥤ 𝒵'} {Pa' : 𝒜 ⥤ 𝒵'} {Pb' : ℬ ⥤ 𝒵'}
    (ta : Pa' ≅ Pa ⋙ Φ) (tb : Pb' ≅ Pb ⋙ Φ) {M : 𝒜} {N : ℬ} (u : Pa.obj M ⟶ Pb.obj N)
    [IsIso u] : IsIso (secMap ta tb u) := by
  unfold secMap
  infer_instance

/-- Restriction through a fully faithful functor is bijective. -/
theorem secMap_bijective {Pa : 𝒜 ⥤ 𝒵} {Pb : ℬ ⥤ 𝒵} {Φ : 𝒵 ⥤ 𝒵'} {Pa' : 𝒜 ⥤ 𝒵'} {Pb' : ℬ ⥤ 𝒵'}
    (ta : Pa' ≅ Pa ⋙ Φ) (tb : Pb' ≅ Pb ⋙ Φ) (hΦ : Φ.FullyFaithful) {M : 𝒜} {N : ℬ} :
    Function.Bijective (secMap ta tb (M := M) (N := N)) := by
  refine ⟨fun u v h => hΦ.map_injective ?_, fun w => ⟨hΦ.preimage (ta.inv.app M ≫ w ≫ tb.hom.app N),
    ?_⟩⟩
  · have := congrArg (fun t => ta.inv.app M ≫ t ≫ tb.hom.app N) h
    simpa [secMap] using this
  · simp [secMap]

/-- Restriction through a fully faithful functor reflects isomorphisms. -/
theorem isIso_of_isIso_secMap {Pa : 𝒜 ⥤ 𝒵} {Pb : ℬ ⥤ 𝒵} {Φ : 𝒵 ⥤ 𝒵'} {Pa' : 𝒜 ⥤ 𝒵'}
    {Pb' : ℬ ⥤ 𝒵'} (ta : Pa' ≅ Pa ⋙ Φ) (tb : Pb' ≅ Pb ⋙ Φ) (hΦ : Φ.FullyFaithful) {M : 𝒜}
    {N : ℬ} (u : Pa.obj M ⟶ Pb.obj N) [IsIso (secMap ta tb u)] : IsIso u := by
  have : IsIso (Φ.map u) := by
    have e : Φ.map u = ta.inv.app M ≫ secMap ta tb u ≫ tb.hom.app N := by simp [secMap]
    rw [e]
    infer_instance
  exact hΦ.isIso_of_isIso_map u

/-- Conjugation by a comparison is restriction through it on both sides. -/
theorem conjHom_eq_secMap {P₁ : 𝒜 ⥤ 𝒵} {P₂ : 𝒜 ⥤ 𝒵'} {Φ : 𝒵 ⥤ 𝒵'} (e : P₂ ≅ P₁ ⋙ Φ) {M N : 𝒜}
    (α : P₁.obj M ⟶ P₁.obj N) : Functor.conjHom e α = secMap e e α :=
  rfl

/-- Inverses of isomorphisms compose in the opposite order when the isomorphisms do. -/
private theorem inv_comp_inv_eq {𝒞 : Type*} [Category* 𝒞] {A B C D : 𝒞} (i₁ : A ≅ B) (i₂ : B ≅ C)
    (j₁ : A ≅ D) (k : D ≅ C) (h : i₁.hom ≫ i₂.hom = j₁.hom ≫ k.hom) :
    k.inv ≫ j₁.inv = i₂.inv ≫ i₁.inv := by
  simpa using congrArg Iso.inv (Iso.ext h : i₁ ≪≫ i₂ = j₁ ≪≫ k).symm

/-- **Restriction composes**, given the associativity coherence of the comparisons. -/
theorem secMap_secMap {Pa : 𝒜 ⥤ 𝒵} {Pb : ℬ ⥤ 𝒵} {Φ : 𝒵 ⥤ 𝒵'} {Pa' : 𝒜 ⥤ 𝒵'}
    {Pb' : ℬ ⥤ 𝒵'} {Φ' : 𝒵' ⥤ 𝒵''} {Pa'' : 𝒜 ⥤ 𝒵''} {Pb'' : ℬ ⥤ 𝒵''} {Φc : 𝒵 ⥤ 𝒵''}
    (ta : Pa' ≅ Pa ⋙ Φ) (tb : Pb' ≅ Pb ⋙ Φ) (ta' : Pa'' ≅ Pa' ⋙ Φ') (tb' : Pb'' ≅ Pb' ⋙ Φ')
    (ta'' : Pa'' ≅ Pa ⋙ Φc) (tb'' : Pb'' ≅ Pb ⋙ Φc) (tc : Φc ≅ Φ ⋙ Φ') {M : 𝒜} {N : ℬ}
    (hMa : ta''.hom.app M ≫ tc.hom.app (Pa.obj M) = ta'.hom.app M ≫ Φ'.map (ta.hom.app M))
    (hNb : tb''.hom.app N ≫ tc.hom.app (Pb.obj N) = tb'.hom.app N ≫ Φ'.map (tb.hom.app N))
    (u : Pa.obj M ⟶ Pb.obj N) :
    secMap ta' tb' (secMap ta tb u) = secMap ta'' tb'' u := by
  have e₁ : ta'.hom.app M ≫ Φ'.map (ta.hom.app M) = ta''.hom.app M ≫ tc.hom.app (Pa.obj M) :=
    hMa.symm
  have e₂ : Φ'.map (tb.inv.app N) ≫ tb'.inv.app N = tc.inv.app (Pb.obj N) ≫ tb''.inv.app N :=
    inv_comp_inv_eq (tb''.app N) (tc.app _) (tb'.app N) (Φ'.mapIso (tb.app N)) hNb
  have e₃ : tc.hom.app (Pa.obj M) ≫ Φ'.map (Φ.map u) = Φc.map u ≫ tc.hom.app (Pb.obj N) :=
    (tc.hom.naturality u).symm
  simp only [secMap, Functor.map_comp, Category.assoc]
  rw [reassoc_of% e₁, e₂, reassoc_of% e₃, Iso.hom_inv_id_app_assoc]

/-- **Restriction commutes with the change of modules along two further functors**, given the
associativity coherence of the comparisons. -/
theorem secMap_push {𝒜₀ ℬ₀ : Type*} [Category* 𝒜₀] [Category* ℬ₀] {Pf : 𝒜₀ ⥤ 𝒜} {Qg : ℬ₀ ⥤ ℬ}
    {Pa : 𝒜 ⥤ 𝒵} {Pb : ℬ ⥤ 𝒵} {Φ : 𝒵 ⥤ 𝒵'} {Pa' : 𝒜 ⥤ 𝒵'} {Pb' : ℬ ⥤ 𝒵'}
    (ta : Pa' ≅ Pa ⋙ Φ) (tb : Pb' ≅ Pb ⋙ Φ) {R1 : 𝒜₀ ⥤ 𝒵} {R1' : 𝒜₀ ⥤ 𝒵'} {R2 : ℬ₀ ⥤ 𝒵}
    {R2' : ℬ₀ ⥤ 𝒵'} (u1 : R1 ≅ Pf ⋙ Pa) (u1' : R1' ≅ Pf ⋙ Pa') (u2 : R2 ≅ Qg ⋙ Pb)
    (u2' : R2' ≅ Qg ⋙ Pb') (v1 : R1' ≅ R1 ⋙ Φ) (v2 : R2' ≅ R2 ⋙ Φ) {M : 𝒜₀} {N : ℬ₀}
    (h1 : v1.hom.app M ≫ Φ.map (u1.hom.app M) = u1'.hom.app M ≫ ta.hom.app (Pf.obj M))
    (h2 : v2.hom.app N ≫ Φ.map (u2.hom.app N) = u2'.hom.app N ≫ tb.hom.app (Qg.obj N))
    (s : Pa.obj (Pf.obj M) ⟶ Pb.obj (Qg.obj N)) :
    u1'.hom.app M ≫ secMap ta tb s ≫ u2'.inv.app N =
      secMap v1 v2 (u1.hom.app M ≫ s ≫ u2.inv.app N) := by
  have e₂ : Φ.map (u2.inv.app N) ≫ v2.inv.app N = tb.inv.app (Qg.obj N) ≫ u2'.inv.app N :=
    inv_comp_inv_eq (u2'.app N) (tb.app _) (v2.app N) (Φ.mapIso (u2.app N)) h2.symm
  simp only [secMap, Functor.map_comp, Category.assoc]
  rw [e₂, reassoc_of% h1]

end CategoryTheory.Functor

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 03LU, the associativity coherence of the comparisons of inverse images, read at a
module.** -/
theorem modulePullbackTriangle_comp_app {V W X Z : AlgebraicSpaces B S hS}
    {f : V ⟶ W} {g : W ⟶ X} {p : X ⟶ Z} {k : V ⟶ X} {q : W ⟶ Z} {r : V ⟶ Z}
    (hk : f ≫ g = k) (hq : g ≫ p = q) (hr : f ≫ q = r) (hkr : k ≫ p = r)
    (K : Modules.{u, u} B S hS Z.1 Z.2) :
    (modulePullbackTriangle B S hS hkr).hom.app K ≫
        (modulePullbackTriangle B S hS hk).hom.app ((modulePullback B S hS p).obj K) =
      (modulePullbackTriangle B S hS hr).hom.app K ≫
        (modulePullback B S hS f).map ((modulePullbackTriangle B S hS hq).hom.app K) := by
  have h := congrArg (fun e => e.hom.app K)
    ((modulePushforwardCoherence B S hS).modulePullbackTriangle_comp hk hq hr hkr)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.associator_hom_app, Category.comp_id] at h
  exact h

/-- **The restriction of a homomorphism between inverse images.**  A homomorphism
`a^*M ⟶ b^*N` of modules on `Z`, for `a : Z ⟶ A` and `b : Z ⟶ B'`, restricts along `φ : Z' ⟶ Z`
to a homomorphism `a'^*M ⟶ b'^*N` for any `a'`, `b'` equal to the composites, read through the
comparisons of Stacks 03LU. -/
def secRestrict {A B' Z Z' : AlgebraicSpaces B S hS} {M : Modules.{u, u} B S hS A.1 A.2}
    {N : Modules.{u, u} B S hS B'.1 B'.2} {a : Z ⟶ A} {b : Z ⟶ B'} {a' : Z' ⟶ A}
    {b' : Z' ⟶ B'} (φ : Z' ⟶ Z) (ha : φ ≫ a = a') (hb : φ ≫ b = b')
    (s : (modulePullback B S hS a).obj M ⟶ (modulePullback B S hS b).obj N) :
    (modulePullback B S hS a').obj M ⟶ (modulePullback B S hS b').obj N :=
  CategoryTheory.Functor.secMap (modulePullbackTriangle B S hS ha)
    (modulePullbackTriangle B S hS hb) s

/-- The restriction of an isomorphism between inverse images is an isomorphism. -/
instance isIso_secRestrict {A B' Z Z' : AlgebraicSpaces B S hS}
    {M : Modules.{u, u} B S hS A.1 A.2} {N : Modules.{u, u} B S hS B'.1 B'.2} {a : Z ⟶ A}
    {b : Z ⟶ B'} {a' : Z' ⟶ A} {b' : Z' ⟶ B'} (φ : Z' ⟶ Z) (ha : φ ≫ a = a') (hb : φ ≫ b = b')
    (s : (modulePullback B S hS a).obj M ⟶ (modulePullback B S hS b).obj N) [IsIso s] :
    IsIso (secRestrict φ ha hb s) :=
  CategoryTheory.Functor.isIso_secMap _ _ s

/-- **Restriction composes.** -/
theorem secRestrict_secRestrict {A B' Z Z' Z'' : AlgebraicSpaces B S hS}
    {M : Modules.{u, u} B S hS A.1 A.2} {N : Modules.{u, u} B S hS B'.1 B'.2} {a : Z ⟶ A}
    {b : Z ⟶ B'} {a' : Z' ⟶ A} {b' : Z' ⟶ B'} {a'' : Z'' ⟶ A} {b'' : Z'' ⟶ B'}
    (φ : Z' ⟶ Z) (ha : φ ≫ a = a') (hb : φ ≫ b = b') (φ' : Z'' ⟶ Z') (ha' : φ' ≫ a' = a'')
    (hb' : φ' ≫ b' = b'') (ha'' : (φ' ≫ φ) ≫ a = a'') (hb'' : (φ' ≫ φ) ≫ b = b'')
    (s : (modulePullback B S hS a).obj M ⟶ (modulePullback B S hS b).obj N) :
    secRestrict φ' ha' hb' (secRestrict φ ha hb s) = secRestrict (φ' ≫ φ) ha'' hb'' s :=
  CategoryTheory.Functor.secMap_secMap _ _ _ _ _ _
    (modulePullbackTriangle B S hS (rfl : φ' ≫ φ = _))
    (modulePullbackTriangle_comp_app rfl ha ha' ha'' M)
    (modulePullbackTriangle_comp_app rfl hb hb' hb'' N) s

/-- Restriction depends on the morphism and not on how its equality with the composites is
proved; equal morphisms restrict equally. -/
theorem secRestrict_congr {A B' Z Z' : AlgebraicSpaces B S hS} {M : Modules.{u, u} B S hS A.1 A.2}
    {N : Modules.{u, u} B S hS B'.1 B'.2} {a : Z ⟶ A} {b : Z ⟶ B'} {a' : Z' ⟶ A}
    {b' : Z' ⟶ B'} {φ φ' : Z' ⟶ Z} (hφ : φ = φ') (ha : φ ≫ a = a') (hb : φ ≫ b = b')
    (ha' : φ' ≫ a = a') (hb' : φ' ≫ b = b')
    (s : (modulePullback B S hS a).obj M ⟶ (modulePullback B S hS b).obj N) :
    secRestrict φ ha hb s = secRestrict φ' ha' hb' s := by
  subst hφ
  rfl

/-- A homomorphism of the inverse images of `f^*M` and `g^*N` along `a` and `b`, read as a
homomorphism of the inverse images of `M` and `N` along the composites. -/
def secPush {Z A₀ B₀ A₁ B₁ : AlgebraicSpaces B S hS} {M : Modules.{u, u} B S hS A₀.1 A₀.2}
    {N : Modules.{u, u} B S hS B₀.1 B₀.2} (a : Z ⟶ A₁) (f : A₁ ⟶ A₀) (b : Z ⟶ B₁) (g : B₁ ⟶ B₀)
    (s : (modulePullback B S hS a).obj ((modulePullback B S hS f).obj M) ⟶
      (modulePullback B S hS b).obj ((modulePullback B S hS g).obj N)) :
    (modulePullback B S hS (a ≫ f)).obj M ⟶ (modulePullback B S hS (b ≫ g)).obj N :=
  (modulePullbackTriangle B S hS (rfl : a ≫ f = _)).hom.app M ≫ s ≫
    (modulePullbackTriangle B S hS (rfl : b ≫ g = _)).inv.app N

/-- Reading an isomorphism along the composites gives an isomorphism. -/
instance isIso_secPush {Z A₀ B₀ A₁ B₁ : AlgebraicSpaces B S hS}
    {M : Modules.{u, u} B S hS A₀.1 A₀.2}
    {N : Modules.{u, u} B S hS B₀.1 B₀.2} (a : Z ⟶ A₁) (f : A₁ ⟶ A₀) (b : Z ⟶ B₁) (g : B₁ ⟶ B₀)
    (s : (modulePullback B S hS a).obj ((modulePullback B S hS f).obj M) ⟶
      (modulePullback B S hS b).obj ((modulePullback B S hS g).obj N)) [IsIso s] :
    IsIso (secPush a f b g s) := by
  unfold secPush
  infer_instance

/-- **Restriction commutes with reading a homomorphism of inverse images of inverse images as one
of inverse images along the composites.** -/
theorem secPush_secRestrict {Z Z' A₀ B₀ A₁ B₁ : AlgebraicSpaces B S hS}
    {M : Modules.{u, u} B S hS A₀.1 A₀.2} {N : Modules.{u, u} B S hS B₀.1 B₀.2} {a : Z ⟶ A₁}
    {b : Z ⟶ B₁} {a' : Z' ⟶ A₁} {b' : Z' ⟶ B₁} (f : A₁ ⟶ A₀) (g : B₁ ⟶ B₀) (φ : Z' ⟶ Z)
    (ha : φ ≫ a = a') (hb : φ ≫ b = b') (ha' : φ ≫ (a ≫ f) = a' ≫ f)
    (hb' : φ ≫ (b ≫ g) = b' ≫ g)
    (s : (modulePullback B S hS a).obj ((modulePullback B S hS f).obj M) ⟶
      (modulePullback B S hS b).obj ((modulePullback B S hS g).obj N)) :
    secPush a' f b' g (secRestrict φ ha hb s) = secRestrict φ ha' hb' (secPush a f b g s) :=
  CategoryTheory.Functor.secMap_push _ _ _ _ _ _ _ _
    (modulePullbackTriangle_comp_app ha rfl ha' rfl M).symm
    (modulePullbackTriangle_comp_app hb rfl hb' rfl N).symm s

/-- Reading homomorphisms of inverse images along the composites is bijective. -/
theorem secPush_bijective {Z A₀ B₀ A₁ B₁ : AlgebraicSpaces B S hS}
    {M : Modules.{u, u} B S hS A₀.1 A₀.2} {N : Modules.{u, u} B S hS B₀.1 B₀.2} (a : Z ⟶ A₁)
    (f : A₁ ⟶ A₀) (b : Z ⟶ B₁) (g : B₁ ⟶ B₀) :
    Function.Bijective (secPush a f b g (M := M) (N := N)) := by
  refine ⟨fun u v h => ?_, fun w => ⟨(modulePullbackTriangle B S hS (rfl : a ≫ f = _)).inv.app M ≫
    w ≫ (modulePullbackTriangle B S hS (rfl : b ≫ g = _)).hom.app N, ?_⟩⟩
  · have := congrArg (fun t => (modulePullbackTriangle B S hS (rfl : a ≫ f = _)).inv.app M ≫ t ≫
      (modulePullbackTriangle B S hS (rfl : b ≫ g = _)).hom.app N) h
    simpa [secPush] using this
  · simp [secPush]

/-- A homomorphism of inverse images is an isomorphism once its reading along the composites is
one. -/
theorem isIso_of_isIso_secPush {Z A₀ B₀ A₁ B₁ : AlgebraicSpaces B S hS}
    {M : Modules.{u, u} B S hS A₀.1 A₀.2} {N : Modules.{u, u} B S hS B₀.1 B₀.2} (a : Z ⟶ A₁)
    (f : A₁ ⟶ A₀) (b : Z ⟶ B₁) (g : B₁ ⟶ B₀)
    (s : (modulePullback B S hS a).obj ((modulePullback B S hS f).obj M) ⟶
      (modulePullback B S hS b).obj ((modulePullback B S hS g).obj N))
    [IsIso (secPush a f b g s)] : IsIso s := by
  have e : s = (modulePullbackTriangle B S hS (rfl : a ≫ f = _)).inv.app M ≫ secPush a f b g s ≫
      (modulePullbackTriangle B S hS (rfl : b ≫ g = _)).hom.app N := by simp [secPush]
  rw [e]
  infer_instance

/-- Restriction followed by the identification of the inverse images along two equal morphisms is
restriction for the other morphism. -/
theorem secRestrict_comp_eqToHom {A B' Z Z' : AlgebraicSpaces B S hS}
    {M : Modules.{u, u} B S hS A.1 A.2} {N : Modules.{u, u} B S hS B'.1 B'.2} {a : Z ⟶ A}
    {b : Z ⟶ B'} {a' : Z' ⟶ A} {b' b'' : Z' ⟶ B'} (φ : Z' ⟶ Z) (ha : φ ≫ a = a')
    (hb : φ ≫ b = b') (hbb : b' = b'')
    (s : (modulePullback B S hS a).obj M ⟶ (modulePullback B S hS b).obj N) :
    secRestrict φ ha hb s ≫ eqToHom (congrArg (fun k => (modulePullback B S hS k).obj N) hbb) =
      secRestrict φ ha (hb.trans hbb) s := by
  subst hbb
  simp only [eqToHom_refl, Category.comp_id]

end AlgebraicGeometry.Space

end
