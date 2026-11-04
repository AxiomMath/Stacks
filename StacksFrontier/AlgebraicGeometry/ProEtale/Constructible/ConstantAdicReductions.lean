module

public import Mathlib.RingTheory.Noetherian.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafIsoDescent
public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.Adic
public import StacksFrontier.CategoryTheory.MittagLefflerSections
public import StacksFrontier.AlgebraicGeometry.ProEtale.ExtensionByZero.AdicSheaves
public import StacksFrontier.RingTheory.AdicCompletion.InverseLimit
public import StacksFrontier.RingTheory.Module.FiniteFromAdicReduction
public import StacksCore.Tactic.StacksAttribute

/-!
# Sheaves of modules with constant adic reductions

Let `Λ` be a Noetherian ring, `I ⊆ Λ` an ideal and `F` a sheaf of `Λ`-modules on the small
pro-étale site of a scheme `X`. If every reduction `F / IⁿF` is a constant sheaf and the first
one is the constant sheaf of a finite module, then there is a single `I`-adically complete
`Λ`-module `M`, finite over `Λ^∧`, whose own reductions `M / IⁿM` have the reductions of `F` as
their constant sheaves: the tower of constant sheaves whose limit is the completed constant sheaf
of `M` is termwise isomorphic to the adic quotient tower of `F`.

## Main definitions

* `AlgebraicGeometry.ProEtale.isTerminalProEtId`: the identity of `X` is a terminal object of
  the small pro-étale site of `X`.
* `AlgebraicGeometry.ProEtale.constantSheafAdjId`: the constant-sheaf adjunction there, with
  global sections taken over that terminal object.
* `AlgebraicGeometry.ProEtale.isQuotientByIso`: the comparison isomorphism between two
  quotients of a sheaf of modules by one ideal.
* `AlgebraicGeometry.ProEtale.constantAdicQuotientTower`: the tower `n ↦ (M / IⁿM)̲` of constant
  sheaves of the adic quotients of a module, whose limit is the completed constant sheaf of `M`.
* `AlgebraicGeometry.ProEtale.adicQuotientCone` and
  `AlgebraicGeometry.ProEtale.constantAdicQuotientCone`: the cones of quotient maps
  `M ⟶ M / IⁿM` and `M̲ ⟶ (M / IⁿM)̲` over that tower and its module-level counterpart.

## Main results

* `AlgebraicGeometry.ProEtale.isAnnihilatedBy_constantSheaf`: the constant sheaf of a module
  annihilated by an ideal is annihilated by that ideal.
* `AlgebraicGeometry.ProEtale.isQuotientBy_constantSheaf`: the constant sheaf of the reduction
  `A ⧸ JA` is the quotient of `A̲` by `J`.
* `AlgebraicGeometry.ProEtale.isQuotientBy_map_of_tower`: in an adic quotient tower the
  transition map `F / IⁿF ⟶ F / IᵐF` exhibits its target as the quotient of its source by `Iᵐ`.
* `AlgebraicGeometry.ProEtale.smul_top_eq_bot_of_constantSheaf_iso`: an ideal annihilating a
  sheaf annihilates the value of a constant sheaf isomorphic to it.
* `AlgebraicGeometry.ProEtale.exists_isAdicComplete_constantSheaf_iso_of_isConstant`: an
  `I`-adically complete module whose tower of constant reductions is termwise isomorphic to the
  adic quotient tower of `F`, from finiteness of the value at every level.
* `AlgebraicGeometry.ProEtale.exists_finite_constantSheaf_iso_of_isConstant`: finiteness of the
  value at level one propagates to every level.
* `AlgebraicGeometry.ProEtale.exists_finite_isAdicComplete_constantSheaf_iso_of_isConstant`:
  the two combined, under the hypotheses of Tag 09BV, with `M` finite over `Λ^∧`. This is the
  part of that tag which produces the coefficient module; the tag's conclusion `F ≅ M̲^∧` needs
  the termwise isomorphisms to be compatible with the transition maps, and is
  `AlgebraicGeometry.ProEtale.exists_iso_completedConstantSheaf_of_isConstant`.
* `AlgebraicGeometry.ProEtale.epi_constantSheaf_map`: the constant sheaf functor preserves
  epimorphisms.
* `AlgebraicGeometry.ProEtale.isQuotientBy_constantAdicQuotientTower_map`: every transition map
  of `constantAdicQuotientTower` exhibits its target as the quotient of its source by the
  relevant power of `I`.
* `AlgebraicGeometry.ProEtale.epi_constantAdicQuotientTower_map`: those transition maps are
  epimorphisms.
* `AlgebraicGeometry.ProEtale.descendsIsos_constantAdicQuotientTower_self` and
  `AlgebraicGeometry.ProEtale.descendsIsos_constantAdicQuotientTower`: isomorphisms descend
  along those transition maps, to the tower itself and to the adic quotient tower of `F`.

## Implementation notes

The adic quotient tower of `F` is not constructed but characterized, by
`AlgebraicGeometry.ProEtale.IsQuotientBy`: its `n`-th term is required to be initial among
morphisms out of `F` to sheaves annihilated by `Iⁿ`. This pins down the actual quotients
`F / IⁿF` and their canonical transition maps up to unique isomorphism, so the hypothesis
speaks about the reductions of `F` and not about some tower merely isomorphic to them.
`isQuotientBy_constantSheaf` transports that characterization from sheaves to modules: it is
proved from the constant-sheaf adjunction at the terminal object of the site, where the
universal property of the quotient module is available, rather than from any construction of
the quotient sheaf.

The descent for morphisms of constant sheaves
(`Stacks.ConstantSheaf.exists_surjective_ker_eq_of_constantSheaf_quotient_iso`) consumes
finiteness of the value at every level, which is more than the source assumes; the source asks
only that `F / IF` be of finite type, equivalently — by Tag 093N (1), for a constant sheaf —
that the value at level one be finite. `exists_finite_constantSheaf_iso_of_isConstant` closes the
difference: `Iⁿ` annihilates the value `N` at level `n`, the reduction `N ⧸ IN` is a quotient of
the value at level one by the asymmetric descent
`Stacks.ConstantSheaf.exists_surjective_of_constantSheaf_iso`, and `N` is then finite by Nakayama
for a nilpotently acting ideal. The `Λ ⧸ Iⁿ`-module structure of the source is not needed; it is
recovered from the tower, each of whose terms is annihilated by `Iⁿ`.

Two hypotheses of the source are absent because this part of its argument does not use them:
`F` is not required to be the limit of its reductions, and `X` is not required to be a weakly
contractible affine scheme. Those enter only in the identification of `F` itself with the
completed constant sheaf. Non-emptiness of the pro-étale topos of `X` is hypothesized instead of
weak contractibility, as the descent for constant sheaves needs it; it fails only for empty `X`,
for which every sheaf of modules vanishes.

### What the compatible choice needs

That identification needs the termwise isomorphisms produced here to be compatible with the
transition maps. The source gets this by making `I_n = Isom(M_n̲, F / IⁿF)` a sheaf torsor under
`Isom(M_n̲, M_n̲)`, deducing from Tag 09BB that the system `(I_n)` is Mittag-Leffler, and taking a
section of the limit of its images over the weakly contractible `X`. There is no torsor notion on
a general site, so the argument is restructured in
`StacksFrontier/CategoryTheory/MittagLefflerSections.lean`: the torsor is globally trivial — the
termwise isomorphisms exist, which is exactly a point of `I_n` — so the set of isomorphisms at
each level is a translate of the set of automorphisms of `M_n̲`, and
`CategoryTheory.Functor.nonempty_natIso_of_isMittagLeffler_isoTower` upgrades termwise
isomorphisms to an isomorphism of towers out of three inputs: the transition maps of the first
tower are epimorphisms, isomorphisms descend along them, and the tower of automorphism sets of
the first tower is Mittag-Leffler.

The first two are supplied here, for the tower `constantAdicQuotientTower` of constant sheaves
of the adic quotients of `M`, by `epi_constantAdicQuotientTower_map` and by
`descendsIsos_constantAdicQuotientTower_self` and `descendsIsos_constantAdicQuotientTower`. The
third is
`AlgebraicGeometry.ProEtale.isMittagLeffler_isoTower_constantAdicQuotientTower`, and the
identification itself is
`AlgebraicGeometry.ProEtale.exists_iso_completedConstantSheaf_of_isConstant`, both in
`StacksFrontier/AlgebraicGeometry/ProEtale/Constructible/ConstantAdicCompletedIso.lean`. They
compare the tower of automorphism sets with the tower `n ↦ Γ(X, Isom_Λ(M_n, M_n)̲)`, which is
Mittag-Leffler as soon as `n ↦ Isom_Λ(M_n, M_n)` is, by
`CategoryTheory.Functor.IsMittagLeffler.comp_type` applied to the functor of types taking a set to
the global sections of its constant sheaf; the comparison is a bijection of systems, and
`CategoryTheory.Functor.isMittagLeffler_of_surjective_natTrans` transfers the condition. Its two
ingredients are `Stacks.ConstantSheaf.constantSheafIsomHom_naturality`, which makes the comparison
of Tag 093T (2) natural in the module arguments along the reduction maps — those are not
isomorphisms — and `Stacks.ConstantSheaf.isoEquivSheafIsomObjIsTerminal`, which identifies the
sections of `Isom` over a terminal object with the isomorphisms of the two sheaves. That the
system `n ↦ Isom_Λ(M_n, M_n)` is Mittag-Leffler is Tag 09BB for a module finite over `Λ^∧` rather
than over `Λ`, which is what `M` is, and is
`Stacks.AdicSystem.CompleteBase.isom_quotient_system_isMittagLeffler_of_finite_adicCompletion`;
the statement available before,
`Stacks.AdicSystem.HomComparison.hom_isom_quotient_systems_mittagLeffler_and_completion`, asks the
module to be finite over the Noetherian base.

## References

* [Stacks Project, Tag 09BV](https://stacks.math.columbia.edu/tag/09BV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry.ProEtale

/-- The identity of `X`, viewed as an object of the small pro-étale site of `X`, is terminal. -/
def isTerminalProEtId (X : Scheme.{u}) : IsTerminal (Scheme.ProEt.mk (𝟙 X)) :=
  IsTerminal.ofUniqueHom
    (fun U => MorphismProperty.Over.homMk U.hom (Category.comp_id _) trivial)
    (fun U m => by
      apply (MorphismProperty.Comma.forgetFullyFaithful
        (Functor.id Scheme.{u}) (Functor.fromPUnit X) _).map_injective
      refine CommaMorphism.ext ?_ (Subsingleton.elim _ _)
      change m.left = U.hom
      exact (Category.comp_id m.left).symm.trans m.w)

variable (X : Scheme.{u}) (Λ : Type v) [CommRing Λ]

section Annihilated

variable [HasWeakSheafify (Scheme.ProEt.topology X) (ModuleCat.{w} Λ)]
  [(Scheme.ProEt.topology X).WEqualsLocallyBijective (ModuleCat.{w} Λ)]
  [(Scheme.ProEt.topology X).HasSheafCompose (forget (ModuleCat.{w} Λ))]

/-- The constant sheaf of a module annihilated by an ideal is annihilated by that ideal. -/
theorem isAnnihilatedBy_constantSheaf (J : Ideal Λ) (B : ModuleCat.{w} Λ)
    (hB : ∀ a ∈ J, ∀ b : B, a • b = 0) :
    IsAnnihilatedBy X Λ J
      ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{w} Λ)).obj B) := by
  intro U a ha x
  refine ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{w} Λ)).obj B).property.isSeparated
    _ _ (Presheaf.imageSieve_mem (Scheme.ProEt.topology X)
      (toSheafify (Scheme.ProEt.topology X) ((Functor.const (X.ProEt)ᵒᵖ).obj B)) x) _ _ ?_
  rintro Y q ⟨m, hm⟩
  have h2 : (((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{w} Λ)).obj B).obj.map q.op).hom x
      = (Stacks.ConstantSheaf.constantUnitApp (Scheme.ProEt.topology X) B (op Y)).hom m := hm.symm
  rw [map_zero, map_smul, h2, ← map_smul, show a • m = 0 from hB a ha m, map_zero]

omit [(Scheme.ProEt.topology X).HasSheafCompose (forget (ModuleCat.{w} Λ))] in
/-- An ideal annihilating a sheaf annihilates the value of a constant sheaf isomorphic to it,
as soon as some object of the site is not sheaf theoretically empty. -/
theorem smul_top_eq_bot_of_constantSheaf_iso (J : Ideal Λ)
    (hne : ∃ U : X.ProEt, (⊥ : Sieve U) ∉ Scheme.ProEt.topology X U) (N : ModuleCat.{w} Λ)
    {H : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{w} Λ)} (hH : IsAnnihilatedBy X Λ J H)
    (e : (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{w} Λ)).obj N ≅ H) :
    J • (⊤ : Submodule Λ (N : Type w)) = ⊥ := by
  obtain ⟨U, hU⟩ := hne
  have hinj : Function.Injective (e.hom.hom.app (op U)).hom :=
    Function.LeftInverse.injective (g := (e.inv.hom.app (op U)).hom) fun y => by
      show ((e.hom ≫ e.inv).hom.app (op U)).hom y = y
      rw [e.hom_inv_id]
      rfl
  refine le_antisymm (Submodule.smul_le.2 fun a ha m _ => ?_) bot_le
  refine (Submodule.mem_bot _).2
    (Stacks.ConstantSheaf.injective_constantUnitApp (Scheme.ProEt.topology X) N hU (hinj ?_))
  rw [map_smul, map_smul, map_zero, map_zero]
  exact hH U a ha _

/-- The constant-sheaf adjunction on the small pro-étale site, with global sections taken over
the identity of `X`. -/
abbrev constantSheafAdjId :
    constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{w} Λ) ⊣
      (sheafSections (Scheme.ProEt.topology X) (ModuleCat.{w} Λ)).obj
        (op (Scheme.ProEt.mk (𝟙 X))) :=
  constantSheafAdj _ _ (isTerminalProEtId X)

omit [(Scheme.ProEt.topology X).WEqualsLocallyBijective (ModuleCat.{w} Λ)]
  [(Scheme.ProEt.topology X).HasSheafCompose (forget (ModuleCat.{w} Λ))] in
/-- Morphisms out of the constant sheaf of a quotient module are determined by their
composition with the constant sheaf of the quotient map. -/
theorem constantSheaf_quotient_hom_ext {A : ModuleCat.{w} Λ} (P : Submodule Λ A)
    {H : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{w} Λ)}
    (φ φ' : (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{w} Λ)).obj
        (ModuleCat.of Λ (A ⧸ P)) ⟶ H)
    (h : (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{w} Λ)).map
          (ModuleCat.ofHom P.mkQ) ≫ φ =
        (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{w} Λ)).map
          (ModuleCat.ofHom P.mkQ) ≫ φ') :
    φ = φ' := by
  have hepi : Epi (ModuleCat.ofHom P.mkQ) :=
    (ModuleCat.epi_iff_surjective _).2 P.mkQ_surjective
  refine (constantSheafAdjId X Λ).homEquiv _ H |>.injective ?_
  have h1 := (constantSheafAdjId X Λ).homEquiv_naturality_left (ModuleCat.ofHom P.mkQ) φ
  have h2 := (constantSheafAdjId X Λ).homEquiv_naturality_left (ModuleCat.ofHom P.mkQ) φ'
  exact (cancel_epi (ModuleCat.ofHom P.mkQ)).1 (h1.symm.trans ((congrArg _ h).trans h2))

/-- The constant sheaf of the reduction `A ⧸ J A` is the quotient of the constant sheaf of `A`
by the ideal `J`: it is annihilated by `J` and initial among morphisms out of `A̲` to sheaves
annihilated by `J`. -/
theorem isQuotientBy_constantSheaf (J : Ideal Λ) (A : ModuleCat.{w} Λ) :
    IsQuotientBy X Λ J
      ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{w} Λ)).obj A)
      ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{w} Λ)).obj
        (ModuleCat.of Λ (A ⧸ (J • ⊤ : Submodule Λ A))))
      ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{w} Λ)).map
        (ModuleCat.ofHom (J • (⊤ : Submodule Λ A)).mkQ)) := by
  refine ⟨isAnnihilatedBy_constantSheaf X Λ J _ ?_, ?_⟩
  · intro a ha b
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    exact (Submodule.Quotient.mk_eq_zero _).2
      (Submodule.smul_mem_smul ha Submodule.mem_top)
  · intro H hH f
    let l := ((constantSheafAdjId X Λ).homEquiv _ H).symm
        (ModuleCat.ofHom ((J • (⊤ : Submodule Λ A)).liftQ
          (((constantSheafAdjId X Λ).homEquiv A H) f).hom (by
            refine Submodule.smul_le.2 fun r hr n _ => ?_
            simp only [LinearMap.mem_ker, map_smul]
            exact hH (Scheme.ProEt.mk (𝟙 X)) r hr _)))
    have hl : (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{w} Λ)).map
        (ModuleCat.ofHom (J • (⊤ : Submodule Λ A)).mkQ) ≫ l = f := by
      refine ((constantSheafAdjId X Λ).homEquiv A H).injective ?_
      rw [(constantSheafAdjId X Λ).homEquiv_naturality_left, Equiv.apply_symm_apply]
      exact ModuleCat.hom_ext (Submodule.liftQ_mkQ _ _ _)
    exact ⟨l, hl, fun g hg => constantSheaf_quotient_hom_ext X Λ _ _ _ (hg.trans hl.symm)⟩

end Annihilated

section QuotientBy

/-- A sheaf annihilated by an ideal is annihilated by every smaller ideal. -/
theorem IsAnnihilatedBy.mono {J J' : Ideal Λ} (hJ : J' ≤ J)
    {H : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{w} Λ)}
    (hH : IsAnnihilatedBy X Λ J H) : IsAnnihilatedBy X Λ J' H :=
  fun U a ha x => hH U a (hJ ha) x

/-- Two quotients of a sheaf of modules by the same ideal are isomorphic, by an isomorphism
carrying one quotient map to the other. -/
def isQuotientByIso {J : Ideal Λ}
    {F G G' : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{w} Λ)} {q : F ⟶ G} {q' : F ⟶ G'}
    (h : IsQuotientBy X Λ J F G q) (h' : IsQuotientBy X Λ J F G' q') : G ≅ G' where
  hom := (h.2 G' h'.1 q').choose
  inv := (h'.2 G h.1 q).choose
  hom_inv_id := ((h.2 G h.1 q).choose_spec.2 _ (by
      change q ≫ ((h.2 G' h'.1 q').choose ≫ (h'.2 G h.1 q).choose) = q
      rw [← Category.assoc, (h.2 G' h'.1 q').choose_spec.1,
        (h'.2 G h.1 q).choose_spec.1])).trans
    ((h.2 G h.1 q).choose_spec.2 (𝟙 G) (Category.comp_id q)).symm
  inv_hom_id := ((h'.2 G' h'.1 q').choose_spec.2 _ (by
      change q' ≫ ((h'.2 G h.1 q).choose ≫ (h.2 G' h'.1 q').choose) = q'
      rw [← Category.assoc, (h'.2 G h.1 q).choose_spec.1,
        (h.2 G' h'.1 q').choose_spec.1])).trans
    ((h'.2 G' h'.1 q').choose_spec.2 (𝟙 G') (Category.comp_id q')).symm

/-- The comparison isomorphism between two quotients by one ideal carries the first quotient
map to the second. -/
theorem isQuotientByIso_hom_comp {J : Ideal Λ}
    {F G G' : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{w} Λ)} {q : F ⟶ G} {q' : F ⟶ G'}
    (h : IsQuotientBy X Λ J F G q) (h' : IsQuotientBy X Λ J F G' q') :
    q ≫ (isQuotientByIso X Λ h h').hom = q' :=
  (h.2 G' h'.1 q').choose_spec.1

/-- Being the quotient by an ideal is transported along an isomorphism of the source. -/
theorem isQuotientBy_of_iso {J : Ideal Λ}
    {F F' G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{w} Λ)} {q : F ⟶ G} (e : F' ≅ F)
    (h : IsQuotientBy X Λ J F G q) : IsQuotientBy X Λ J F' G (e.hom ≫ q) := by
  refine ⟨h.1, fun H hH f => ⟨(h.2 H hH (e.inv ≫ f)).choose, ?_, fun y hy => ?_⟩⟩
  · show (e.hom ≫ q) ≫ _ = f
    rw [Category.assoc, (h.2 H hH (e.inv ≫ f)).choose_spec.1, ← Category.assoc,
      e.hom_inv_id, Category.id_comp]
  · change (e.hom ≫ q) ≫ y = f at hy
    refine (h.2 H hH (e.inv ≫ f)).choose_spec.2 y ?_
    show q ≫ y = e.inv ≫ f
    rw [← hy, Category.assoc, ← Category.assoc e.inv e.hom, e.inv_hom_id, Category.id_comp]

variable (I : Ideal Λ)
  (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{w} Λ))
  (Q : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology X) (ModuleCat.{w} Λ))
  (q : (Functor.const ℕᵒᵖ).obj F ⟶ Q)

/-- The transition map `F / IⁿF ⟶ F / IᵐF` of the adic quotient tower, for `m ≤ n`, exhibits
its target as the quotient of its source by `Iᵐ`. -/
theorem isQuotientBy_map_of_tower
    (hq : ∀ n : ℕ, IsQuotientBy X Λ (I ^ n) F (Q.obj (op n)) (q.app (op n)))
    {m n : ℕ} (hmn : m ≤ n) :
    IsQuotientBy X Λ (I ^ m) (Q.obj (op n)) (Q.obj (op m)) (Q.map (homOfLE hmn).op) := by
  have hnat : q.app (op n) ≫ Q.map (homOfLE hmn).op = q.app (op m) := by
    simpa using (q.naturality (homOfLE hmn).op).symm
  refine ⟨(hq m).1, fun H hH g =>
    ⟨((hq m).2 H hH (q.app (op n) ≫ g)).choose, ?_, fun y hy => ?_⟩⟩
  · have hbig := (hq n).2 H
      (hH.mono X Λ (Ideal.pow_le_pow_right hmn)) (q.app (op n) ≫ g)
    show Q.map (homOfLE hmn).op ≫ _ = g
    refine (hbig.choose_spec.2 _ ?_).trans (hbig.choose_spec.2 g rfl).symm
    show q.app (op n) ≫ Q.map (homOfLE hmn).op ≫ _ = _
    rw [← Category.assoc, hnat]
    exact ((hq m).2 H hH (q.app (op n) ≫ g)).choose_spec.1
  · change Q.map (homOfLE hmn).op ≫ y = g at hy
    refine ((hq m).2 H hH (q.app (op n) ≫ g)).choose_spec.2 y ?_
    show q.app (op m) ≫ y = q.app (op n) ≫ g
    rw [← hnat, Category.assoc, hy]

/-- `isQuotientBy_map_of_tower`, for an arbitrary morphism of `ℕᵒᵖ`. -/
private theorem isQuotientBy_tower_map
    (hq : ∀ n : ℕ, IsQuotientBy X Λ (I ^ n) F (Q.obj (op n)) (q.app (op n)))
    ⦃m n : ℕᵒᵖ⦄ (f : m ⟶ n) :
    IsQuotientBy X Λ (I ^ n.unop) (Q.obj m) (Q.obj n) (Q.map f) := by
  rw [show f = (homOfLE (leOfHom f.unop)).op from Subsingleton.elim _ _]
  exact isQuotientBy_map_of_tower X Λ I F Q q hq (leOfHom f.unop)

end QuotientBy

section Main

variable [IsNoetherianRing Λ]
  [HasSheafify (Scheme.ProEt.topology X) (ModuleCat.{w} Λ)]
  [(Scheme.ProEt.topology X).WEqualsLocallyBijective (ModuleCat.{w} Λ)]
  [(Scheme.ProEt.topology X).HasSheafCompose (forget (ModuleCat.{w} Λ))]

/-- If `N̲ ≅ Qₙ` in an adic quotient tower, then `(N ⧸ IᵐN)̲ ≅ Qₘ` for `m ≤ n`. -/
private def constantSheaf_quotient_iso_tower (I : Ideal Λ)
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{w} Λ))
    (Q : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology X) (ModuleCat.{w} Λ))
    (q : (Functor.const ℕᵒᵖ).obj F ⟶ Q)
    (hq : ∀ n : ℕ, IsQuotientBy X Λ (I ^ n) F (Q.obj (op n)) (q.app (op n)))
    {m n : ℕ} (hmn : m ≤ n) {N : ModuleCat.{w} Λ}
    (e : (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{w} Λ)).obj N ≅ Q.obj (op n)) :
    (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{w} Λ)).obj
        (ModuleCat.of Λ ((N : Type w) ⧸ (I ^ m • ⊤ : Submodule Λ (N : Type w)))) ≅
      Q.obj (op m) :=
  isQuotientByIso X Λ (isQuotientBy_constantSheaf X Λ (I ^ m) N)
    (isQuotientBy_of_iso X Λ e (isQuotientBy_map_of_tower X Λ I F Q q hq hmn))

/-- If every reduction `F / IⁿF` of a sheaf of `Λ`-modules on the small pro-étale site is the
constant sheaf of a finite `Λ`-module, then there is an `I`-adically complete `Λ`-module `M`,
with every reduction `M / IⁿM` finite over `Λ`, whose tower of constant reductions — the tower
whose limit is the completed constant sheaf of `M` — is termwise isomorphic to the adic quotient
tower of `F`.

The hypothesis is stronger than the source's, which asks finite type of `F / IF` alone;
`exists_finite_isAdicComplete_constantSheaf_iso_of_isConstant` is the same statement under the
source's hypotheses and is the declaration that carries the attribute. -/
theorem exists_isAdicComplete_constantSheaf_iso_of_isConstant (I : Ideal Λ)
    (hne : ∃ U : X.ProEt, (⊥ : Sieve U) ∉ Scheme.ProEt.topology X U)
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{w} Λ))
    (Q : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology X) (ModuleCat.{w} Λ))
    (q : (Functor.const ℕᵒᵖ).obj F ⟶ Q)
    (hq : ∀ n : ℕ, IsQuotientBy X Λ (I ^ n) F (Q.obj (op n)) (q.app (op n)))
    (hconst : ∀ n : ℕ, ∃ N : ModuleCat.{w} Λ, Module.Finite Λ (N : Type w) ∧
      Nonempty ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{w} Λ)).obj N ≅
        Q.obj (op n))) :
    ∃ M : ModuleCat.{w} Λ, IsAdicComplete I (M : Type w) ∧
      Module.Finite Λ ((M : Type w) ⧸ (I • ⊤ : Submodule Λ (M : Type w))) ∧
      (∀ n : ℕ, Module.Finite Λ ((M : Type w) ⧸ (I ^ n • ⊤ : Submodule Λ (M : Type w)))) ∧
      ∀ n : ℕ, Nonempty ((adicQuotientModuleSystem Λ I M ⋙
        constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{w} Λ)).obj (op n) ≅
          Q.obj (op n)) := by
  classical
  have hIFG : I.FG := IsNoetherian.noetherian I
  choose N hNfin hNiso using hconst
  set e : ∀ n : ℕ, (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{w} Λ)).obj (N n) ≅
      Q.obj (op n) := fun n => (hNiso n).some
  have key : ∀ n : ℕ,
      (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{w} Λ)).obj
          (ModuleCat.of Λ ((N (n + 1) : Type w) ⧸
            (I ^ n • ⊤ : Submodule Λ (N (n + 1) : Type w)))) ≅
        (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{w} Λ)).obj (N n) := fun n =>
    constantSheaf_quotient_iso_tower X Λ I F Q q hq (Nat.le_succ n) (e (n + 1)) ≪≫ (e n).symm
  have hψ : ∀ n : ℕ, ∃ ψ : N (n + 1) ⟶ N n, Function.Surjective ψ.hom ∧
      LinearMap.ker ψ.hom = (I ^ n • ⊤ : Submodule Λ (N (n + 1) : Type w)) := by
    intro n
    have := hNfin (n + 1)
    have := hNfin n
    have : Module.Finite Λ ((N (n + 1) : Type w) ⧸
        (I ^ n • ⊤ : Submodule Λ (N (n + 1) : Type w))) := Module.Finite.quotient _ _
    have := Module.finitePresentation_of_finite Λ ((N (n + 1) : Type w) ⧸
      (I ^ n • ⊤ : Submodule Λ (N (n + 1) : Type w)))
    have := Module.finitePresentation_of_finite Λ (N n : Type w)
    exact Stacks.ConstantSheaf.exists_surjective_ker_eq_of_constantSheaf_quotient_iso
      (Scheme.ProEt.topology X) hne (N (n + 1)) (N n) _ (key n)
  choose ψ hψsurj hψker using hψ
  let S : Stacks.AdicCompletion.InverseLimit.InverseSystem I :=
    { M := fun n => (N n : Type w)
      π := fun n => (ψ n).hom
      surjective := hψsurj
      ker_π := hψker }
  refine ⟨ModuleCat.of Λ S.limit, S.isAdicComplete hIFG, ?_, fun n => ?_, fun n => ?_⟩
  · have := hNfin 1
    exact Module.Finite.equiv
      ((Submodule.quotEquivOfEq _ _ (by rw [pow_one])).trans (S.quotientEquiv hIFG 1)).symm
  · have := hNfin n
    exact Module.Finite.equiv (S.quotientEquiv hIFG n).symm
  · exact ⟨(constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{w} Λ)).mapIso
      (LinearEquiv.toModuleIso (S.quotientEquiv hIFG n)) ≪≫ e n⟩

/-- If every reduction `F / IⁿF` of a sheaf of `Λ`-modules is a constant sheaf and `F / IF` is
the constant sheaf of a finite module, then every reduction is the constant sheaf of a finite
module: `Iⁿ` annihilates the value at level `n`, whose reduction modulo `I` is a quotient of the
value at level one, so Nakayama applies. -/
theorem exists_finite_constantSheaf_iso_of_isConstant (I : Ideal Λ)
    (hne : ∃ U : X.ProEt, (⊥ : Sieve U) ∉ Scheme.ProEt.topology X U)
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{w} Λ))
    (Q : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology X) (ModuleCat.{w} Λ))
    (q : (Functor.const ℕᵒᵖ).obj F ⟶ Q)
    (hq : ∀ n : ℕ, IsQuotientBy X Λ (I ^ n) F (Q.obj (op n)) (q.app (op n)))
    (hconst : ∀ n : ℕ, ∃ N : ModuleCat.{w} Λ,
      Nonempty ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{w} Λ)).obj N ≅
        Q.obj (op n)))
    (hfin : ∃ N : ModuleCat.{w} Λ, Module.Finite Λ (N : Type w) ∧
      Nonempty ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{w} Λ)).obj N ≅
        Q.obj (op 1)))
    (n : ℕ) :
    ∃ N : ModuleCat.{w} Λ, Module.Finite Λ (N : Type w) ∧
      Nonempty ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{w} Λ)).obj N ≅
        Q.obj (op n)) := by
  obtain ⟨N, ⟨e⟩⟩ := hconst n
  obtain ⟨N₁, hN₁fin, ⟨e₁⟩⟩ := hfin
  refine ⟨N, ?_, ⟨e⟩⟩
  have hnil : I ^ n • (⊤ : Submodule Λ (N : Type w)) = ⊥ :=
    smul_top_eq_bot_of_constantSheaf_iso X Λ (I ^ n) hne N (hq n).1 e
  have hred : Module.Finite Λ ((N : Type w) ⧸ (I • ⊤ : Submodule Λ (N : Type w))) := by
    match n, e, hnil with
    | 0, _, hnil =>
      rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul] at hnil
      have : Module.Finite Λ (N : Type w) := Module.finite_def.mpr (hnil ▸ Submodule.fg_bot)
      exact Module.Finite.quotient _ _
    | (n' + 1), e, _ =>
      have hcomp := constantSheaf_quotient_iso_tower X Λ I F Q q hq (Nat.le_add_left 1 n') e
      have := Module.finitePresentation_of_finite Λ (N₁ : Type w)
      have hfin1 : Module.Finite Λ
          ((N : Type w) ⧸ (I ^ 1 • ⊤ : Submodule Λ (N : Type w))) :=
        Stacks.ConstantSheaf.finite_of_constantSheaf_iso (Scheme.ProEt.topology X) hne N₁ _
          (e₁ ≪≫ hcomp.symm)
      exact hfin1.equiv (Submodule.quotEquivOfEq _ _ (by rw [pow_one]))
  exact Module.Finite.of_pow_smul_top_eq_bot I (N : Type w) hnil hred

/-- **Stacks 09BV, the coefficient module.** Let `Λ` be Noetherian, `I ⊆ Λ` an ideal and `F` a
sheaf of `Λ`-modules on the small pro-étale site whose reductions `F / IⁿF` are constant sheaves
and whose first reduction is of finite type. Then there is an `I`-adically complete `Λ`-module
`M`, finite over `Λ^∧` and with every reduction `M / IⁿM` finite over `Λ`, whose tower of constant
reductions is termwise isomorphic to the adic quotient tower of `F`. -/
@[stacks 09BV "the finite complete coefficient module and its termwise constant reductions"]
theorem exists_finite_isAdicComplete_constantSheaf_iso_of_isConstant (I : Ideal Λ)
    (hne : ∃ U : X.ProEt, (⊥ : Sieve U) ∉ Scheme.ProEt.topology X U)
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{w} Λ))
    (Q : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology X) (ModuleCat.{w} Λ))
    (q : (Functor.const ℕᵒᵖ).obj F ⟶ Q)
    (hq : ∀ n : ℕ, IsQuotientBy X Λ (I ^ n) F (Q.obj (op n)) (q.app (op n)))
    (hconst : ∀ n : ℕ, ∃ N : ModuleCat.{w} Λ,
      Nonempty ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{w} Λ)).obj N ≅
        Q.obj (op n)))
    (hfin : ∃ N : ModuleCat.{w} Λ, Module.Finite Λ (N : Type w) ∧
      Nonempty ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{w} Λ)).obj N ≅
        Q.obj (op 1))) :
    ∃ M : ModuleCat.{w} Λ, IsAdicComplete I (M : Type w) ∧
      Module.Finite Λ ((M : Type w) ⧸ (I • ⊤ : Submodule Λ (M : Type w))) ∧
      Module.Finite (AdicCompletion I Λ) (AdicCompletion I (M : Type w)) ∧
      (∀ n : ℕ, Module.Finite Λ ((M : Type w) ⧸ (I ^ n • ⊤ : Submodule Λ (M : Type w)))) ∧
      ∀ n : ℕ, Nonempty ((adicQuotientModuleSystem Λ I M ⋙
        constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{w} Λ)).obj (op n) ≅
          Q.obj (op n)) := by
  obtain ⟨M, hMcomplete, hMfin, hMfinpow, hMiso⟩ :=
    exists_isAdicComplete_constantSheaf_iso_of_isConstant X Λ I hne F Q q hq
      (exists_finite_constantSheaf_iso_of_isConstant X Λ I hne F Q q hq hconst hfin)
  exact ⟨M, hMcomplete, hMfin,
    Module.Finite.adicCompletion_of_finite_quotient_smul_top (IsNoetherian.noetherian I)
      (M : Type w) hMfin, hMfinpow, hMiso⟩

end Main

section Compatible

variable [HasWeakSheafify (Scheme.ProEt.topology X) (ModuleCat.{w} Λ)]
  [(Scheme.ProEt.topology X).WEqualsLocallyBijective (ModuleCat.{w} Λ)]
  [(Scheme.ProEt.topology X).HasSheafCompose (forget (ModuleCat.{w} Λ))]
  (I : Ideal Λ) (M : ModuleCat.{w} Λ)

omit [(Scheme.ProEt.topology X).WEqualsLocallyBijective (ModuleCat.{w} Λ)]
  [(Scheme.ProEt.topology X).HasSheafCompose (forget (ModuleCat.{w} Λ))] in
/-- The constant sheaf functor preserves epimorphisms, being a left adjoint. -/
theorem epi_constantSheaf_map {A B : ModuleCat.{w} Λ} (φ : A ⟶ B) [Epi φ] :
    Epi ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{w} Λ)).map φ) :=
  ⟨fun {H} u v huv => ((constantSheafAdjId X Λ).homEquiv _ H).injective
    ((cancel_epi φ).1 ((((constantSheafAdjId X Λ).homEquiv_naturality_left φ u).symm.trans
      (congrArg _ huv)).trans ((constantSheafAdjId X Λ).homEquiv_naturality_left φ v)))⟩

/-- The tower of constant sheaves of the adic quotients `M / IⁿM`, whose limit is the completed
constant sheaf of `M`. -/
abbrev constantAdicQuotientTower :
    ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology X) (ModuleCat.{w} Λ) :=
  adicQuotientModuleSystem Λ I M ⋙ constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{w} Λ)

/-- The transition map of the adic quotient tower of a module is reduction of a representative:
it carries the class of `x` in `M / Iⁿ⁺¹M` to the class of `x` in `M / IⁿM`. -/
theorem adicQuotient_transitionMap_mk (n : ℕ) (x : (M : Type w)) :
    ((adicQuotientModuleSystem Λ I M).map (homOfLE (Nat.le_succ n)).op).hom
        (Submodule.Quotient.mk x) = Submodule.Quotient.mk x := by
  simp only [adicQuotientModuleSystem, Functor.ofOpSequence_map_homOfLE_succ]
  rfl

/-- The quotient map `M ⟶ M / Iⁿ⁺¹M` followed by the transition map of the adic quotient tower
is the quotient map `M ⟶ M / IⁿM`. -/
theorem mkQ_comp_adicQuotient_transitionMap (n : ℕ) :
    ModuleCat.ofHom (I ^ (n + 1) • (⊤ : Submodule Λ (M : Type w))).mkQ ≫
        (adicQuotientModuleSystem Λ I M).map (homOfLE (Nat.le_succ n)).op =
      ModuleCat.ofHom (I ^ n • (⊤ : Submodule Λ (M : Type w))).mkQ :=
  ModuleCat.hom_ext (LinearMap.ext fun x => adicQuotient_transitionMap_mk Λ I M n x)

/-- The transition maps of the adic quotient tower of a module are surjective. -/
theorem surjective_adicQuotient_transitionMap (n : ℕ) :
    Function.Surjective
      ((adicQuotientModuleSystem Λ I M).map (homOfLE (Nat.le_succ n)).op).hom := by
  intro y
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  exact ⟨Submodule.Quotient.mk x, adicQuotient_transitionMap_mk Λ I M n x⟩

omit [(Scheme.ProEt.topology X).WEqualsLocallyBijective (ModuleCat.{w} Λ)]
  [(Scheme.ProEt.topology X).HasSheafCompose (forget (ModuleCat.{w} Λ))] in
/-- Every transition map of the tower of constant sheaves of the adic quotients of `M` is an
epimorphism. -/
theorem epi_constantAdicQuotientTower_map ⦃m n : ℕᵒᵖ⦄ (f : m ⟶ n) :
    Epi ((constantAdicQuotientTower X Λ I M).map f) := by
  refine Functor.epi_map_of_epi_succ (fun k => ?_) f
  have : Epi ((adicQuotientModuleSystem Λ I M).map (homOfLE (Nat.le_succ k)).op) :=
    (ModuleCat.epi_iff_surjective _).2 (surjective_adicQuotient_transitionMap Λ I M k)
  exact epi_constantSheaf_map X Λ
    ((adicQuotientModuleSystem Λ I M).map (homOfLE (Nat.le_succ k)).op)

/-- The cone of quotient maps `M ⟶ M / IⁿM`. -/
def adicQuotientCone : (Functor.const ℕᵒᵖ).obj M ⟶ adicQuotientModuleSystem Λ I M :=
  NatTrans.ofOpSequence
    (fun n => ModuleCat.ofHom (I ^ n • (⊤ : Submodule Λ (M : Type w))).mkQ)
    (fun n => (Category.id_comp _).trans (mkQ_comp_adicQuotient_transitionMap Λ I M n).symm)

/-- The cone of quotient maps `M̲ ⟶ (M / IⁿM)̲`. -/
def constantAdicQuotientCone :
    (Functor.const ℕᵒᵖ).obj
        ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{w} Λ)).obj M) ⟶
      constantAdicQuotientTower X Λ I M :=
  NatTrans.ofOpSequence
    (fun n => (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{w} Λ)).map
      ((adicQuotientCone Λ I M).app (op n)))
    (fun n => by
      have hnat := (adicQuotientCone Λ I M).naturality (homOfLE (Nat.le_add_right n 1)).op
      simp only [Functor.const_obj_map] at hnat ⊢
      rw [show (constantAdicQuotientTower X Λ I M).map (homOfLE (Nat.le_add_right n 1)).op =
            (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{w} Λ)).map
              ((adicQuotientModuleSystem Λ I M).map (homOfLE (Nat.le_add_right n 1)).op) from rfl,
        ← CategoryTheory.Functor.map_comp, ← hnat, CategoryTheory.Functor.map_comp,
        CategoryTheory.Functor.map_id])

/-- In the tower of constant sheaves of the adic quotients of `M`, every transition map exhibits
its target as the quotient of its source by the relevant power of `I`: the cone of quotient maps
out of `M̲` realizes each term as a quotient of `M̲`, by `isQuotientBy_constantSheaf`, so
`isQuotientBy_map_of_tower` applies. -/
theorem isQuotientBy_constantAdicQuotientTower_map ⦃m n : ℕᵒᵖ⦄ (f : m ⟶ n) :
    IsQuotientBy X Λ (I ^ n.unop) ((constantAdicQuotientTower X Λ I M).obj m)
      ((constantAdicQuotientTower X Λ I M).obj n)
      ((constantAdicQuotientTower X Λ I M).map f) := by
  exact isQuotientBy_tower_map X Λ I
    ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{w} Λ)).obj M)
    (constantAdicQuotientTower X Λ I M) (constantAdicQuotientCone X Λ I M)
    (fun k => isQuotientBy_constantSheaf X Λ (I ^ k) M) f

omit [HasWeakSheafify (Scheme.ProEt.topology X) (ModuleCat.{w} Λ)]
  [(Scheme.ProEt.topology X).WEqualsLocallyBijective (ModuleCat.{w} Λ)]
  [(Scheme.ProEt.topology X).HasSheafCompose (forget (ModuleCat.{w} Λ))] in
/-- Isomorphisms descend along the transition maps of two towers each of whose transition maps
exhibits its target as the quotient by the relevant power of `I`: the induced map of quotients is
the descent, and `isQuotientByIso_hom_comp` is the square it has to make commute. -/
theorem descendsIsos_of_isQuotientBy_map
    {A B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology X) (ModuleCat.{w} Λ)}
    (hA : ∀ ⦃m n : ℕᵒᵖ⦄ (f : m ⟶ n),
      IsQuotientBy X Λ (I ^ n.unop) (A.obj m) (A.obj n) (A.map f))
    (hB : ∀ ⦃m n : ℕᵒᵖ⦄ (f : m ⟶ n),
      IsQuotientBy X Λ (I ^ n.unop) (B.obj m) (B.obj n) (B.map f)) :
    Functor.DescendsIsos A B := fun _ _ f α =>
  ⟨isQuotientByIso X Λ (hA f) (isQuotientBy_of_iso X Λ α (hB f)),
    isQuotientByIso_hom_comp X Λ (hA f) (isQuotientBy_of_iso X Λ α (hB f))⟩

/-- Isomorphisms descend along the transition maps of the tower of constant sheaves of the adic
quotients of `M`. -/
theorem descendsIsos_constantAdicQuotientTower_self :
    Functor.DescendsIsos (constantAdicQuotientTower X Λ I M)
      (constantAdicQuotientTower X Λ I M) :=
  descendsIsos_of_isQuotientBy_map X Λ I (isQuotientBy_constantAdicQuotientTower_map X Λ I M)
    (isQuotientBy_constantAdicQuotientTower_map X Λ I M)

/-- Isomorphisms descend from the tower of constant sheaves of the adic quotients of `M` to the
adic quotient tower of a sheaf `F`. -/
theorem descendsIsos_constantAdicQuotientTower
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{w} Λ))
    (Q : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology X) (ModuleCat.{w} Λ))
    (q : (Functor.const ℕᵒᵖ).obj F ⟶ Q)
    (hq : ∀ n : ℕ, IsQuotientBy X Λ (I ^ n) F (Q.obj (op n)) (q.app (op n))) :
    Functor.DescendsIsos (constantAdicQuotientTower X Λ I M) Q :=
  descendsIsos_of_isQuotientBy_map X Λ I (isQuotientBy_constantAdicQuotientTower_map X Λ I M)
    (isQuotientBy_tower_map X Λ I F Q q hq)

end Compatible

end AlgebraicGeometry.ProEtale

end
