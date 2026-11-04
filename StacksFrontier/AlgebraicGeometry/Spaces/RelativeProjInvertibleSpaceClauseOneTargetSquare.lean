module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOneHone
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOnePaste

/-!
# The target square of clause (1) of Stacks 0D2Z at a scheme point of `U(ψ)`

Clause (1) of [Stacks, Tag 0D2Z] at a scheme point `w : W ⟶ U(ψ)` is pasted from three squares
(`…InvertibleTwistingRestriction.modulePullback_map_comp_eq_of_shaped_squares`).  This file proves
the **target square**: the source identification of the square (the four factors of
`…InvertibleTwistingRestriction.clauseOnePointSourceIso`), followed by the module attached to the
right-hand side of the middle square and by the identification `…chartTargetIso` of the target of
the chart map, is the inverse image along `w` of the `ψ` leg.

The square is stated for a family of inverse images `Φ` with comparisons `κ` satisfying the
associativity coherence of the comparisons of Stacks 03LU. In that setting the two canonical
identifications of `w^*(π_{U(ψ)}^*𝒜_d)` with `(f ∘ w)^*𝒜_d` agree
(`AlgebraicGeometry.Space.comparison_chain_eq`).

## Main results

* `AlgebraicGeometry.Space.comparison_chain_eq`: the coherence of the comparisons of Stacks 03LU
  at the composites of clause (1).
* `AlgebraicGeometry.Space.comp_comp_eq_map_of_target_squares`: the target square of clause (1)
  at a scheme point, for a family of inverse images `Φ` with comparisons `κ`.
* `…InvertibleTwistingRestriction.quasicoherentPullbackCompIso_hom_comp_pointComparison`: the
  scheme-level identity of the target square.

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)

universe u m

namespace AlgebraicGeometry.Space

section Coherence

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (Φ : ∀ {X Y : AlgebraicSpaces B S hS}, (X ⟶ Y) →
    Modules.{u, u} B S hS Y.1 Y.2 ⥤ Modules.{u, u} B S hS X.1 X.2)
  (κ : ∀ {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z), Φ g ⋙ Φ f ≅ Φ (f ≫ g))

/-- The inverse image of a transport along `k = k'`, followed by the comparison for `p` and `k'`,
is the comparison for `p` and `k` followed by the transport along `p ≫ k = p ≫ k'`, for a family
of inverse images `Φ` with comparisons `κ`. -/
theorem map_eqToHom_comp_comparison_hom_app {R U Y : AlgebraicSpaces B S hS}
    (p : R ⟶ U) {k k' : U ⟶ Y} (h : k = k') (M : Modules.{u, u} B S hS Y.1 Y.2) :
    (Φ p).map (eqToHom (congrArg (fun k => (Φ k).obj M) h)) ≫ (κ p k').hom.app M =
      (κ p k).hom.app M ≫
        eqToHom (congrArg (fun k => (Φ k).obj M) (congrArg (fun k => p ≫ k) h)) := by
  subst h
  simp

/-- A transport along `g = g'`, followed by the comparison for `g'` and `π`, is the comparison for
`g` and `π` followed by the transport along `g ≫ π = g' ≫ π`. -/
theorem eqToHom_comp_comparison_hom_app {R P Y : AlgebraicSpaces B S hS} {g g' : R ⟶ P}
    (π : P ⟶ Y) (h : g = g') (M : Modules.{u, u} B S hS Y.1 Y.2) :
    eqToHom (congrArg (fun k => (Φ k).obj ((Φ π).obj M)) h) ≫ (κ g' π).hom.app M =
      (κ g π).hom.app M ≫
        eqToHom (congrArg (fun k => (Φ k).obj M) (congrArg (fun k => k ≫ π) h)) := by
  subst h
  simp

/-- The inverse comparison for `f` and `g`, followed by the inverse image along `f` of a transport
along `g = g'`, is the transport along `f ≫ g = f ≫ g'` followed by the inverse comparison. -/
theorem comparison_inv_app_comp_map_eqToHom {R Fs Y : AlgebraicSpaces B S hS} (f : R ⟶ Fs)
    {g g' : Fs ⟶ Y} (h : g = g') (M : Modules.{u, u} B S hS Y.1 Y.2) :
    (κ f g).inv.app M ≫ (Φ f).map (eqToHom (congrArg (fun k => (Φ k).obj M) h)) =
      eqToHom (congrArg (fun k => (Φ k).obj M) (congrArg (fun k => f ≫ k) h)) ≫
        (κ f g').inv.app M := by
  subst h
  simp

/-- The inverse image along `p` of the inverse comparison for `ι` and `f`, followed by that of
the comparison, is the identity. -/
theorem map_comparison_inv_app_comp_map_hom_app {R U X Y : AlgebraicSpaces B S hS}
    (p : R ⟶ U) (ι : U ⟶ X) (f : X ⟶ Y) (M : Modules.{u, u} B S hS Y.1 Y.2) :
    (Φ p).map ((κ ι f).inv.app M) ≫ (Φ p).map ((κ ι f).hom.app M) = 𝟙 _ :=
  ((Φ p).map_comp _ _).symm.trans
    ((congrArg (Φ p).map ((κ ι f).inv_hom_id_app M)).trans ((Φ p).map_id _))

/-- **The canonical identifications of clause (1) at a scheme point agree**, for a family of
inverse images `Φ` with comparisons `κ` satisfying the associativity coherence (the coherence of
the comparisons of Stacks 03LU): for `ι ≫ f = a ≫ π`, `p ≫ a = c ≫ φ`, `φ ≫ π = q ≫ v`,
`c ≫ q = r`, `r ≫ v = v'`, `p ≫ ι = x` and `x ≫ f = v'`, the two composites of comparisons and
transports `p^*((ι ≫ f)^*M) ⟶ v'^*M`, through `c^*φ^*π^*` and through `x^*f^*`, agree. -/
theorem comparison_chain_eq
    (hA : ∀ {W Y Y' Y'' : AlgebraicSpaces B S hS} (a : W ⟶ Y) (b : Y ⟶ Y') (c : Y' ⟶ Y'')
      (M : Modules.{u, u} B S hS Y''.1 Y''.2),
      (κ a b).hom.app ((Φ c).obj M) ≫ (κ (a ≫ b) c).hom.app M =
        (Φ a).map ((κ b c).hom.app M) ≫ (κ a (b ≫ c)).hom.app M)
    (hAi : ∀ {W Y Y' Y'' : AlgebraicSpaces B S hS} (a : W ⟶ Y) (b : Y ⟶ Y') (c : Y' ⟶ Y'')
      (M : Modules.{u, u} B S hS Y''.1 Y''.2),
      (κ (a ≫ b) c).inv.app M ≫ (κ a b).inv.app ((Φ c).obj M) =
        (κ a (b ≫ c)).inv.app M ≫ (Φ a).map ((κ b c).inv.app M))
    (hMI : ∀ {W Y Y' Y'' : AlgebraicSpaces B S hS} (a : W ⟶ Y) (b : Y ⟶ Y') (c : Y' ⟶ Y'')
      (M : Modules.{u, u} B S hS Y''.1 Y''.2),
      (Φ a).map ((κ b c).inv.app M) ≫ (κ a b).hom.app ((Φ c).obj M) =
        (κ a (b ≫ c)).hom.app M ≫ (κ (a ≫ b) c).inv.app M)
    (hIM : ∀ {W Y Y' Y'' : AlgebraicSpaces B S hS} (a : W ⟶ Y) (b : Y ⟶ Y') (c : Y' ⟶ Y'')
      (M : Modules.{u, u} B S hS Y''.1 Y''.2),
      (κ a b).inv.app ((Φ c).obj M) ≫ (Φ a).map ((κ b c).hom.app M) =
        (κ (a ≫ b) c).hom.app M ≫ (κ a (b ≫ c)).inv.app M)
    {R Fs U P Y X : AlgebraicSpaces B S hS}
    (p : R ⟶ U) (a : U ⟶ P) (π : P ⟶ Y) (ι : U ⟶ X) (f : X ⟶ Y) (hk : ι ≫ f = a ≫ π)
    (c : R ⟶ Fs) (φ : Fs ⟶ P) (hab : p ≫ a = c ≫ φ)
    (q : Fs ⟶ R) (v : R ⟶ Y) (hφ : φ ≫ π = q ≫ v)
    (r : R ⟶ R) (hcq : c ≫ q = r) (v' : R ⟶ Y) (hv : r ≫ v = v')
    (x : R ⟶ X) (hx : p ≫ ι = x) (hxv : x ≫ f = v') (M : Modules.{u, u} B S hS Y.1 Y.2) :
    (Φ p).map (eqToHom (congrArg (fun k => (Φ k).obj M) hk) ≫ (κ a π).inv.app M) ≫
      ((κ p a).hom.app ((Φ π).obj M) ≫
        eqToHom (congrArg (fun k => (Φ k).obj ((Φ π).obj M)) hab) ≫
        (κ c φ).inv.app ((Φ π).obj M)) ≫
      (Φ c).map ((κ φ π).hom.app M ≫ eqToHom (congrArg (fun k => (Φ k).obj M) hφ) ≫
          (κ q v).inv.app M) ≫
      (κ c q).hom.app ((Φ v).obj M) ≫
      eqToHom (congrArg (fun k => (Φ k).obj ((Φ v).obj M)) hcq) ≫
      (κ r v).hom.app M ≫ eqToHom (congrArg (fun k => (Φ k).obj M) hv) =
    (Φ p).map ((κ ι f).inv.app M) ≫ (κ p ι).hom.app ((Φ f).obj M) ≫
      eqToHom (congrArg (fun k => (Φ k).obj ((Φ f).obj M)) hx) ≫
      (κ x f).hom.app M ≫ eqToHom (congrArg (fun k => (Φ k).obj M) hxv) := by
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% (hMI p a π M), reassoc_of% (map_eqToHom_comp_comparison_hom_app Φ κ p hk M),
    reassoc_of% (hIM c φ π M), reassoc_of% (eqToHom_comp_comparison_hom_app Φ κ π hab M),
    Iso.inv_hom_id_app_assoc, reassoc_of% (comparison_inv_app_comp_map_eqToHom Φ κ c hφ M),
    ← reassoc_of% (hAi c q v M), Iso.inv_hom_id_app_assoc,
    reassoc_of% (eqToHom_comp_comparison_hom_app Φ κ v hcq M), Iso.inv_hom_id_app_assoc,
    reassoc_of% (eqToHom_comp_comparison_hom_app Φ κ f hx M), reassoc_of% (hA p ι f M),
    reassoc_of% (map_comparison_inv_app_comp_map_hom_app Φ κ p ι f M)]
  simp only [eqToHom_trans]

/-- The inverse image along `k` of a morphism commutes with the transport along `k = k'`. -/
theorem map_comp_eqToHom_comparison {R Y : AlgebraicSpaces B S hS} {k k' : R ⟶ Y} (h : k = k')
    {N N' : Modules.{u, u} B S hS Y.1 Y.2} (g : N ⟶ N') :
    (Φ k).map g ≫ eqToHom (congrArg (fun k => (Φ k).obj N') h) =
      eqToHom (congrArg (fun k => (Φ k).obj N) h) ≫ (Φ k').map g := by
  subst h
  simp

/-- **The target square of clause (1) at a scheme point, at variables**, for a family of inverse
images `Φ` with comparisons `κ` satisfying the associativity coherence.  The source identification
`K = p^*(e_k ≫ κ⁻¹) ≫ τ ≫ c^*χ ≫ ρ_c`, with `χ` the chain `φ^*π^*M ≅ (φ ≫ π)^*M = (q ≫ v)^*M ≅
q^*v^*M ≅ q^*Z ≅ Z_q`, followed by `Ψ = Φ_Γ ≫ Φ_ψ` and `T = θ⁻¹ ≫ e_x ≫ κ⁻¹`, is `p^*b` for
`b = κ⁻¹ ≫ ι^*ψ_d`, granted the composition law of the identifications `ρ` (`hcomp`), their
naturality along `r = c ≫ q` (`hsite`), the scheme-level identity `hΓ` and the square `hTZ` of
`ψ_d` at the point `x`. -/
theorem comp_comp_eq_map_of_target_squares
    (hA : ∀ {W Y Y' Y'' : AlgebraicSpaces B S hS} (a : W ⟶ Y) (b : Y ⟶ Y') (c : Y' ⟶ Y'')
      (M : Modules.{u, u} B S hS Y''.1 Y''.2),
      (κ a b).hom.app ((Φ c).obj M) ≫ (κ (a ≫ b) c).hom.app M =
        (Φ a).map ((κ b c).hom.app M) ≫ (κ a (b ≫ c)).hom.app M)
    (hAi : ∀ {W Y Y' Y'' : AlgebraicSpaces B S hS} (a : W ⟶ Y) (b : Y ⟶ Y') (c : Y' ⟶ Y'')
      (M : Modules.{u, u} B S hS Y''.1 Y''.2),
      (κ (a ≫ b) c).inv.app M ≫ (κ a b).inv.app ((Φ c).obj M) =
        (κ a (b ≫ c)).inv.app M ≫ (Φ a).map ((κ b c).inv.app M))
    (hMI : ∀ {W Y Y' Y'' : AlgebraicSpaces B S hS} (a : W ⟶ Y) (b : Y ⟶ Y') (c : Y' ⟶ Y'')
      (M : Modules.{u, u} B S hS Y''.1 Y''.2),
      (Φ a).map ((κ b c).inv.app M) ≫ (κ a b).hom.app ((Φ c).obj M) =
        (κ a (b ≫ c)).hom.app M ≫ (κ (a ≫ b) c).inv.app M)
    (hIM : ∀ {W Y Y' Y'' : AlgebraicSpaces B S hS} (a : W ⟶ Y) (b : Y ⟶ Y') (c : Y' ⟶ Y'')
      (M : Modules.{u, u} B S hS Y''.1 Y''.2),
      (κ a b).inv.app ((Φ c).obj M) ≫ (Φ a).map ((κ b c).hom.app M) =
        (κ (a ≫ b) c).hom.app M ≫ (κ a (b ≫ c)).inv.app M)
    {R Fs U P Y X : AlgebraicSpaces B S hS}
    {p : R ⟶ U} {a : U ⟶ P} {π : P ⟶ Y} {ι : U ⟶ X} {f : X ⟶ Y} {hk : ι ≫ f = a ≫ π}
    {c : R ⟶ Fs} {φ : Fs ⟶ P} {hab : p ≫ a = c ≫ φ}
    {q : Fs ⟶ R} {v : R ⟶ Y} {hφ : φ ≫ π = q ≫ v}
    {r : R ⟶ R} (hcq : c ≫ q = r) (hv : r ≫ v = v)
    {x : R ⟶ X} (hx : x = p ≫ ι) (hxv : x ≫ f = v)
    {M : Modules.{u, u} B S hS Y.1 Y.2} {Lx : Modules.{u, u} B S hS X.1 X.2}
    {ψd : (Φ f).obj M ⟶ Lx}
    {Zr Qc Zcq Lr : Modules.{u, u} B S hS R.1 R.2} {Zq : Modules.{u, u} B S hS Fs.1 Fs.2}
    {ζ : (Φ v).obj M ≅ Zr} {ρq : (Φ q).obj Zr ≅ Zq} {ρc : (Φ c).obj Zq ≅ Qc}
    {ρr : (Φ r).obj Zr ≅ Zcq} {Fq : Qc ⟶ Zcq} {Fc : Zcq ⟶ Zr} {FG₁ : Qc ⟶ Zr} {FG₂ : Zr ⟶ Lr}
    {θT : (Φ x).obj Lx ≅ Lr}
    {τZ : (Φ (c ≫ q)).obj Zr ⟶ (Φ r).obj Zr}
    (hτZ : τZ = eqToHom (congrArg (fun k => (Φ k).obj Zr) hcq))
    {τv : (Φ (r ≫ v)).obj M ⟶ (Φ v).obj M} (hτv : τv = eqToHom (congrArg (fun k => (Φ k).obj M) hv))
    {τx : (Φ (x ≫ f)).obj M ⟶ (Φ v).obj M}
    (hτx : τx = eqToHom (congrArg (fun k => (Φ k).obj M) hxv))
    (hcomp : (κ c q).hom.app Zr ≫ τZ ≫ ρr.hom = (Φ c).map ρq.hom ≫ ρc.hom ≫ Fq)
    (hsite : (Φ r).map ζ.hom ≫ ρr.hom ≫ Fc = ((κ r v).hom.app M ≫ τv) ≫ ζ.hom)
    (hΓ : Fq ≫ Fc = FG₁)
    (hTZ : (κ x f).hom.app M ≫ τx ≫ ζ.hom ≫ FG₂ = (Φ x).map ψd ≫ θT.hom)
    {K : (Φ p).obj ((Φ (ι ≫ f)).obj M) ⟶ Qc} {Ψ : Qc ⟶ Lr} {T : Lr ⟶ (Φ p).obj ((Φ ι).obj Lx)}
    {b : (Φ (ι ≫ f)).obj M ⟶ (Φ ι).obj Lx}
    {κ₁ : (Φ p).obj ((Φ (ι ≫ f)).obj M) ⟶ (Φ p).obj ((Φ a).obj ((Φ π).obj M))}
    {τ₁ : (Φ p).obj ((Φ a).obj ((Φ π).obj M)) ⟶ (Φ c).obj ((Φ φ).obj ((Φ π).obj M))}
    {χ : (Φ φ).obj ((Φ π).obj M) ⟶ Zq}
    (hK : K = κ₁ ≫ τ₁ ≫ (Φ c).map χ ≫ ρc.hom)
    (hκ₁ : κ₁ = (Φ p).map (eqToHom (congrArg (fun k => (Φ k).obj M) hk) ≫ ((κ a π).app M).inv))
    (hτ₁ : τ₁ = (κ p a).hom.app ((Φ π).obj M) ≫
      eqToHom (congrArg (fun k => (Φ k).obj ((Φ π).obj M)) hab) ≫ (κ c φ).inv.app ((Φ π).obj M))
    (hχ : χ = ((κ φ π).app M).hom ≫ (eqToIso (congrArg (fun k => (Φ k).obj M) hφ)).hom ≫
      ((κ q v).app M).symm.hom ≫ ((Φ q).mapIso ζ).hom ≫ ρq.hom)
    (hΨ : Ψ = FG₁ ≫ FG₂)
    (hT : T = θT.symm.hom ≫ (eqToIso (congrArg (fun k => (Φ k).obj Lx) hx)).hom ≫
      ((κ p ι).app Lx).symm.hom)
    (hb : b = ((κ ι f).app M).inv ≫ (Φ ι).map ψd) :
    K ≫ Ψ ≫ T = (Φ p).map b := by
  subst hK hκ₁ hτ₁ hχ hΨ hT hb hx hΓ hτZ hτv hτx
  have hC := comparison_chain_eq Φ κ hA hAi hMI hIM p a π ι f hk c φ hab q v hφ r hcq v hv
    (p ≫ ι) rfl hxv M
  simp only [Functor.map_comp, Category.assoc] at hC
  simp only [Iso.app_hom, Iso.app_inv, Iso.symm_hom, eqToIso.hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hcomp]
  rw [reassoc_of% ((κ c q).hom.naturality ζ.hom)]
  rw [reassoc_of% (map_comp_eqToHom_comparison Φ hcq ζ.hom)]
  rw [reassoc_of% hsite]
  rw [reassoc_of% hC, reassoc_of% hTZ, Iso.hom_inv_id_assoc]
  simp only [eqToHom_refl, Category.id_comp]
  rw [← reassoc_of% ((κ p ι).hom.naturality ψd)]
  simp

end Coherence


end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)

section Concrete

attribute [local instance 5000] AlgebraicGeometry.Space.SmallEtale.instHasSheafify
  AlgebraicGeometry.Space.SmallEtale.instWEqualsLocallyBijective

variable {s : RelativeProjSituation.{u, m}}
  {X : AlgebraicSpaces s.shrink.site s.shrink.base s.shrink.containsBase} {f : X ⟶ s.shrink.space}
  {L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O)}
  [hL : Stacks.SheafOfModules.IsInvertible
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L]
  {ψ : SheafOfModules.GradedAlgebra.UnitalHom
    ((gradedPull (X := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X)
      (Y := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase s.shrink.space)
      (smallEtaleRingedToposHom s.shrink.site s.shrink.base s.shrink.containsBase f)).obj
        s.shrink.algebra)
    (Stacks.SheafOfModules.TensorPower.laurentAlgebra
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L)}
  {W : BigFppfOver s.shrink.site s.shrink.base s.shrink.containsBase}
  (w : yoneda.obj W ⟶ (locusSpaceOfUnitalHom s f L ψ).obj) (d : ℕ)

/-- The section `c_w` of the fibre `W ×_Y P ⟶ W` at a scheme point of `U(ψ)`, on the points. -/
theorem yoneda_map_chartSection_comp_fibreHom :
    yoneda.map ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w) ≫
      s.relativeProjPoints.fibreHom W (locusPoint w ≫ f.hom)) ≫ (locusPoint w ≫ f.hom) =
        locusPoint w ≫ f.hom :=
  (congrArg (fun g => yoneda.map g ≫ (locusPoint w ≫ f.hom))
    ((ofUnitalHom s f L ψ).chartSection_fibreHom (locusPoint w) (locusOpen_locusPoint w))).trans
    ((congrArg (· ≫ (locusPoint w ≫ f.hom)) (yoneda.map_id _)).trans (Category.id_comp _))

set_option maxHeartbeats 800000 in
-- elaborating the statement and its `rfl` at the chart data exceeds the default limit
/-- **The scheme-level identity of the target square**: the contraction of the two pullbacks along
the section `c_w` and the fibre `q`, followed by the comparison of restricted algebras along
`c_w ≫ q = 𝟙`, is the canonical identification `c_w^*(q^*𝒜_d) ≅ (𝟙)^*𝒜_d ≅ 𝒜_d` of the middle
square. -/
theorem quasicoherentPullbackCompIso_hom_comp_pointComparison :
    (quasicoherentPullbackCompIso s.site s.base s.containsBase
        ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
        (s.relativeProjPoints.fibreHom W (locusPoint w ≫ f.hom))
        (s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ))).hom ≫
      (ObjectProperty.homMk ((pointComparison (B := s.site) (S := s.base) (hS := s.containsBase)
        (X := s.space) s.shrink.algebra
        ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w) ≫
          s.relativeProjPoints.fibreHom W (locusPoint w ≫ f.hom))
        (locusPoint w ≫ f.hom) (locusPoint w ≫ f.hom)
        (yoneda_map_chartSection_comp_fibreHom w)).app (d : ℤ)) :
        quasicoherentPullbackObj s.site s.base s.containsBase
          ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w) ≫
            s.relativeProjPoints.fibreHom W (locusPoint w ≫ f.hom))
          (s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ)) ⟶
        s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ)) =
    (ObjectProperty.homMk (Stacks.AlgebraicGeometry.ModuleLimits.canHom
          ((BigFppfOver.toScheme s.site s.base s.containsBase).map
            ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w)))
          (s.fibreToBase W (locusPoint w ≫ f.hom))
          (𝟙 ((BigFppfOver.toScheme s.site s.base s.containsBase).obj W))
          (toScheme_map_chartSection_comp_fibreToBase s f L ψ (locusPoint w)
            (locusOpen_locusPoint w))
          (s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ)).obj ≫
        (Scheme.Modules.pullbackId _).hom.app
          (s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ)).obj) :
        quasicoherentPullbackObj s.site s.base s.containsBase
            ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
            (quasicoherentPullbackObj s.site s.base s.containsBase
              (s.relativeProjPoints.fibreHom W (locusPoint w ≫ f.hom))
              (s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ))) ⟶
          s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ)) := by
  refine ObjectProperty.hom_ext _ ?_
  have h := pointComparison_app_eq_of_eq_id (B := s.site) (S := s.base) (hS := s.containsBase)
    (X := s.space) s.shrink.algebra s.shrink.isQuasicoherent
    ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w) ≫
      s.relativeProjPoints.fibreHom W (locusPoint w ≫ f.hom))
    ((ofUnitalHom s f L ψ).chartSection_fibreHom (locusPoint w) (locusOpen_locusPoint w))
    (locusPoint w ≫ f.hom) (yoneda_map_chartSection_comp_fibreHom w) (d : ℤ)
  refine (congrArg (_ ≫ ·) h).trans ?_
  rfl

end Concrete

end AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

end
