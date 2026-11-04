module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.ProjectiveSpaceQuotPairs
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.SchemeRepresentation
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.SiteRepresentable

/-!
# `Quot^P` of `𝒪` on `ℙⁿ_U ⟶ U` is represented by `U × Quot^P_{𝒪/ℙⁿ_ℤ/ℤ}`

The subfunctor `Quot^P` of the Quot presheaf of `𝒪_{ℙⁿ_U}/ℙⁿ_U/U`
(`AlgebraicGeometry.ProjectiveQuotOverSpace.hilbertSubfunctor`) is `T ↦ Hom(T, U) × Quot^P(T)`,
where `Quot^P = Quot^P_{𝒪/ℙⁿ_ℤ/ℤ}` is the functor on schemes
`AlgebraicGeometry.ProjectiveQuot.hilbertFunctor n 1 P`. That functor is represented by a scheme
`X_P` proper over `Spec ℤ` (`AlgebraicGeometry.ProjectiveQuot.exists_isProper_iso_hilbertFunctor`,
the scheme-level Stacks 0DPA), which is an object of the site, so `Quot^P` is represented on the
site by the product `U × X_P`.

## Main results

* `AlgebraicGeometry.C1590Private.hilbertSubfunctorReprIso`: the representation by
  `U × Quot^P_{𝒪/ℙⁿ_ℤ/ℤ}`, with `Quot^P_{𝒪/ℙⁿ_ℤ/ℤ}` (`hilbertQuotScheme n P`) independent of `U`.
* `AlgebraicGeometry.C1590Private.exists_iso_hilbertSubfunctor`: `Quot^P` is represented by an
  object of the site.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.C1590Private

open ProjectiveQuot ProjectiveQuotOverSpace

universe u

variable {B : BigFppfSite.{u}} {n : ℕ} {U : BigFppfOver B integerBase B.contains_integerBase}

local notation "𝒯" => BigFppfOver.toScheme B integerBase B.contains_integerBase

/-- The site `BigFppfOver B integerBase _` has binary products. -/
local instance : HasBinaryProducts (BigFppfOver B integerBase B.contains_integerBase) :=
  hasBinaryProducts_of_hasTerminal_and_pullbacks _

/-- `pairsPresheaf` is functorial in the presheaf on schemes. -/
def pairsPresheafMapIso {S S' : Scheme.{u}ᵒᵖ ⥤ Type (u + 1)} (e : S ≅ S') :
    pairsPresheaf U S ≅ pairsPresheaf U S' :=
  NatIso.ofComponents (fun T => (Equiv.prodCongr (Equiv.refl _)
    (e.app (Opposite.op ((𝒯).obj T.unop))).toEquiv).toIso) fun g => by
      ext p
      exact Prod.ext rfl (types_congr_hom (e.hom.naturality ((𝒯).map g.unop).op) p.2)

/-- **`T ↦ Hom(T, U) × Hom(T, X)` is represented by `U × X`**, for a scheme `X` of the site. -/
def pairsPresheafYonedaIso {X : Scheme.{u}} (hX : B.Contains X) :
    pairsPresheaf U (yoneda.obj X ⋙ uliftFunctor.{u + 1}) ≅
      yoneda.obj (U ⨯ CurveFamily.ofScheme (hZ := B.contains_integerBase) X hX) ⋙
        uliftFunctor.{u + 1} :=
  NatIso.ofComponents (fun T => Equiv.toIso
    { toFun := fun p => ULift.up (prod.lift p.1 ((homOfSchemeEquiv hX T.unop).symm p.2.down))
      invFun := fun c => (c.down ≫ prod.fst,
        ULift.up (homOfSchemeEquiv hX T.unop (c.down ≫ prod.snd)))
      left_inv := fun p => by
        refine Prod.ext (prod.lift_fst _ _) (ULift.ext _ _ ?_)
        change homOfSchemeEquiv hX T.unop (prod.lift _ _ ≫ prod.snd) = p.2.down
        rw [prod.lift_snd, Equiv.apply_symm_apply]
      right_inv := fun c => by
        refine ULift.ext _ _ (prod.hom_ext (prod.lift_fst _ _) ?_)
        rw [prod.lift_snd, Equiv.symm_apply_apply] }) fun {T T'} g => by
    ext p
    refine ULift.ext _ _ (prod.hom_ext ?_ ?_)
    · change prod.lift (g.unop ≫ p.1) _ ≫ prod.fst = (g.unop ≫ prod.lift p.1 _) ≫ prod.fst
      rw [prod.lift_fst, Category.assoc, prod.lift_fst]
    · change prod.lift (g.unop ≫ p.1) _ ≫ prod.snd = (g.unop ≫ prod.lift p.1 _) ≫ prod.snd
      rw [prod.lift_snd, Category.assoc, prod.lift_snd]
      apply (homOfSchemeEquiv hX T'.unop).injective
      rw [Equiv.apply_symm_apply]
      change (𝒯).map g.unop ≫ p.2.down =
        (𝒯).map (g.unop ≫ (homOfSchemeEquiv hX T.unop).symm p.2.down)
      rw [Functor.map_comp]
      exact congrArg _ ((homOfSchemeEquiv hX T.unop).apply_symm_apply p.2.down).symm

/-- A family with Hilbert polynomial `P` is in particular a family of quotients. -/
theorem mem_families_of_mem_hilbertFamilies {r : ℕ} {T : Scheme.{u}} {P : Polynomial ℚ}
    {K : Subobject (freeModule n r T)} (h : K ∈ hilbertFamilies n r P T) : K ∈ families n r T :=
  h.1

/-- Rebuilding a pair from its two members, in the presence of a left inverse. -/
theorem apply_pair_eq {X : Type*} {α : Type*} {β : Type*} {q : β → Prop}
    (f : X → α × Subtype q) (g : α × Subtype q → X) (hgf : ∀ a, g (f a) = a) (a : X) :
    g ((f a).1, ⟨(f a).2.1, (f a).2.2⟩) = a :=
  hgf a

variable (P : Polynomial ℚ)

/-- `Quot^P` of `𝒪_{ℙⁿ_U}/ℙⁿ_U/U` at one scheme of the site. -/
def hilbertSubfunctorPairsEquiv (T : (BigFppfOver B integerBase B.contains_integerBase)ᵒᵖ) :
    (hilbertSubfunctor (projectiveSpaceFrame n U) P).toFunctor.obj T ≃
      (T.unop ⟶ U) × hilbertFamilies n 1 P ((𝒯).obj T.unop) where
  toFun x := (((quotPairsIso (n := n) (U := U)).hom.app T x.1).1,
    ⟨((quotPairsIso (n := n) (U := U)).hom.app T x.1).2.1,
      (mem_hilbertSubfunctor_iff_quotPairsIso P T x.1).1 x.2⟩)
  invFun p := ⟨(quotPairsIso (n := n) (U := U)).inv.app T
      ((p.1, ⟨p.2.1, mem_families_of_mem_hilbertFamilies p.2.2⟩) :
        (T.unop ⟶ U) × families n 1 ((𝒯).obj T.unop)),
    (mem_hilbertSubfunctor_iff_quotPairsIso P T _).2 (by
      have h := Iso.inv_hom_id_app_apply (quotPairsIso (n := n) (U := U)) T
        ((p.1, ⟨p.2.1, mem_families_of_mem_hilbertFamilies p.2.2⟩) :
          (T.unop ⟶ U) × families n 1 ((𝒯).obj T.unop))
      have h' : (((quotPairsIso (n := n) (U := U)).hom.app T
          ((quotPairsIso (n := n) (U := U)).inv.app T
            ((p.1, ⟨p.2.1, mem_families_of_mem_hilbertFamilies p.2.2⟩) :
              (T.unop ⟶ U) × families n 1 ((𝒯).obj T.unop)))).2.1 :
            Subobject (freeModule n 1 ((𝒯).obj T.unop))) = p.2.1 :=
        congrArg (fun z => z.2.1) h
      rw [h']
      exact p.2.2)⟩
  left_inv x := Subtype.ext (apply_pair_eq (β := Subobject (freeModule n 1 ((𝒯).obj T.unop)))
    (q := fun K => K ∈ families n 1 ((𝒯).obj T.unop))
    ((quotPairsIso (n := n) (U := U)).hom.app T) ((quotPairsIso (n := n) (U := U)).inv.app T)
    (Iso.hom_inv_id_app_apply (quotPairsIso (n := n) (U := U)) T) x.1)
  right_inv p := by
    have h := Iso.inv_hom_id_app_apply (quotPairsIso (n := n) (U := U)) T
      ((p.1, ⟨p.2.1, mem_families_of_mem_hilbertFamilies p.2.2⟩) :
        (T.unop ⟶ U) × families n 1 ((𝒯).obj T.unop))
    exact Prod.ext (congrArg Prod.fst h :) (Subtype.ext (congrArg (fun q => q.2.1) h :))

/-- `Quot^P` of `𝒪_{ℙⁿ_U}/ℙⁿ_U/U` is `T ↦ Hom(T, U) × Quot^P_{𝒪/ℙⁿ/ℤ}(T)`. -/
def hilbertSubfunctorPairsIso :
    (hilbertSubfunctor (projectiveSpaceFrame n U) P).toFunctor ≅
      pairsPresheaf U (hilbertFunctor.{u} n 1 P) :=
  NatIso.ofComponents (fun T => (hilbertSubfunctorPairsEquiv P T).toIso) fun {T T'} g => by
    ext x
    have h := types_congr_hom ((quotPairsIso (n := n) (U := U)).hom.naturality g) x.1
    exact Prod.ext (congrArg Prod.fst h :) (Subtype.ext (congrArg (fun q => q.2.1) h :))

variable (n) in
/-- The scheme `Quot^P_{𝒪/ℙⁿ_ℤ/ℤ}` representing `AlgebraicGeometry.ProjectiveQuot.hilbertFunctor`
(the scheme-level Stacks 0DPA), chosen once and for all. -/
def hilbertQuotScheme : Scheme.{u} :=
  (exists_isProper_iso_hilbertFunctor.{u} n 1 le_rfl P).choose

variable (n) in
/-- `Quot^P_{𝒪/ℙⁿ_ℤ/ℤ}` is proper over `Spec ℤ`. -/
theorem isProper_hilbertQuotScheme : IsProper (terminal.from (hilbertQuotScheme.{u} n P)) :=
  (exists_isProper_iso_hilbertFunctor.{u} n 1 le_rfl P).choose_spec.1

variable (n) in
/-- The functor `Quot^P_{𝒪/ℙⁿ_ℤ/ℤ}` is represented by `hilbertQuotScheme n P`. -/
def hilbertQuotSchemeIso :
    hilbertFunctor.{u} n 1 P ≅ yoneda.obj (hilbertQuotScheme n P) ⋙ uliftFunctor.{u + 1} :=
  (exists_isProper_iso_hilbertFunctor.{u} n 1 le_rfl P).choose_spec.2.some

variable (B n) in
/-- `Quot^P_{𝒪/ℙⁿ_ℤ/ℤ}` lies in the site, being proper over `Spec ℤ`. -/
theorem contains_hilbertQuotScheme : B.Contains (hilbertQuotScheme n P) :=
  contains_of_isProper_terminal_from B (isProper_hilbertQuotScheme n P)

variable (B n) in
/-- `Quot^P_{𝒪/ℙⁿ_ℤ/ℤ}`, as an object of the site. -/
abbrev hilbertQuotSite : BigFppfOver B integerBase B.contains_integerBase :=
  CurveFamily.ofScheme (hZ := B.contains_integerBase) (hilbertQuotScheme n P)
    (contains_hilbertQuotScheme B n P)

/-- **`Quot^P` of `𝒪_{ℙⁿ_U}/ℙⁿ_U/U` is represented by `U × Quot^P_{𝒪/ℙⁿ_ℤ/ℤ}`.** -/
def hilbertSubfunctorReprIso :
    (hilbertSubfunctor (projectiveSpaceFrame n U) P).toFunctor ≅
      yoneda.obj (U ⨯ hilbertQuotSite B n P) ⋙ uliftFunctor.{u + 1} :=
  hilbertSubfunctorPairsIso P ≪≫ pairsPresheafMapIso (hilbertQuotSchemeIso n P) ≪≫
    pairsPresheafYonedaIso (contains_hilbertQuotScheme B n P)

/-- **`Quot^P` of `𝒪_{ℙⁿ_U}/ℙⁿ_U/U` is represented by an object of the site.** -/
theorem exists_iso_hilbertSubfunctor :
    ∃ V : BigFppfOver B integerBase B.contains_integerBase,
      Nonempty ((hilbertSubfunctor (projectiveSpaceFrame n U) P).toFunctor ≅
        yoneda.obj V ⋙ uliftFunctor.{u + 1}) :=
  ⟨_, ⟨hilbertSubfunctorReprIso P⟩⟩

end AlgebraicGeometry.C1590Private

end
