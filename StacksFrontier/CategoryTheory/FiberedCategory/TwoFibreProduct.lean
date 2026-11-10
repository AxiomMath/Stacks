module

public import StacksFrontier.CategoryTheory.FiberedCategory.Amelioration
public import StacksFrontier.CategoryTheory.TwoFibreProductOver

/-!
# The 2-fibre product of fibred categories is fibred (Stacks 02XQ)

Fix a base category `𝒞`. Let `p𝒳 : 𝒳 ⥤ 𝒞`, `p𝒴 : 𝒴 ⥤ 𝒞`, `p𝒮 : 𝒮 ⥤ 𝒞` be fibred
categories over `𝒞` and let `F : 𝒳 ⥤ 𝒮`, `G : 𝒴 ⥤ 𝒮` be 1-morphisms of fibred categories
over `𝒞`. Stacks 02XQ (Lemma 4.33.10) asserts two things about the 2-fibre product
`𝒳 ×_𝒮 𝒴` of Stacks 0040, whose construction is `CategoryTheory.TwoFibreProductOver`:
its structure functor to `𝒞` is again a fibred category, and the two projections are
again 1-morphisms of fibred categories.

Both come from one analysis of when a morphism of the 2-fibre product is strongly
cartesian: a morphism `Φ = (a, b)` lying over `f` is strongly cartesian for the structure
functor exactly when its two components are strongly cartesian for `p𝒳` and `p𝒴`. The
hypotheses on `F` and `G` are essential in both directions — without `G.map Φ.b` being
strongly cartesian in `𝒮` the comparison square of the universal lift cannot be produced,
and the hypothesis-free statement is false.

Fibredness supplies the components of a lift, and the vertical comparison isomorphism of
the lift is then produced by the universal property of the strongly cartesian `G.map b`;
this is where verticality of the comparison isomorphism (rather than Mathlib's arbitrary
isomorphism of `Limits.CategoricalPullback`, which is the 2-fibre product of plain
categories, Stacks 003R) is used.
-/

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]
variable {𝒳 : Type u₂} [Category.{v₂} 𝒳]
variable {𝒴 : Type u₃} [Category.{v₃} 𝒴]
variable {𝒮 : Type u₄} [Category.{v₄} 𝒮]

namespace TwoFibreProductOver

variable {p𝒳 : 𝒳 ⥤ 𝒞} {p𝒴 : 𝒴 ⥤ 𝒞} {p𝒮 : 𝒮 ⥤ 𝒞} {F : 𝒳 ⥤ 𝒮} {G : 𝒴 ⥤ 𝒮}

/-- **The comparison square of a componentwise factorisation is automatic.** Let `Φ : P ⟶ Q`
have `p𝒴`-strongly cartesian `𝒴`-component over `f`, and let `Φ' : P' ⟶ Q` factor
componentwise through `Φ` as `χa` and `χb`, both lying over one morphism `g` of the base.
Then the pair `(χa, χb)` satisfies the comparison-square condition of a morphism `P' ⟶ P`,
because both sides of that square become the square of `Φ'` after composing with the
`p𝒮`-strongly cartesian `G.map Φ.b`. -/
lemma w_of_isStronglyCartesian
    (hF : Functor.IsFibredOneMorphism p𝒳 p𝒮 F) (hG : Functor.IsFibredOneMorphism p𝒴 p𝒮 G)
    {P Q P' : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G} (f : P.base ⟶ Q.base) (Φ : P ⟶ Q)
    (hb : p𝒴.IsStronglyCartesian f Φ.b) {g : P'.base ⟶ P.base} {χa : P'.x ⟶ P.x}
    (hχa : p𝒳.IsHomLift g χa) {χb : P'.y ⟶ P.y} (hχb : p𝒴.IsHomLift g χb) (Φ' : P' ⟶ Q)
    (hχa_fac : χa ≫ Φ.a = Φ'.a) (hχb_fac : χb ≫ Φ.b = Φ'.b) :
    F.map χa ≫ P.iso.hom = P'.iso.hom ≫ G.map χb := by
  -- `G.map Φ.b` is strongly cartesian over `f`, since `G` preserves strongly cartesian
  -- morphisms; this is what makes the square provable.
  have hGΦb : p𝒮.IsStronglyCartesian f (G.map Φ.b) := hG.map_isStronglyCartesian f Φ.b hb
  have hFχa : p𝒮.IsHomLift g (F.map χa) := hF.map_isHomLift g χa
  have hGχb : p𝒮.IsHomLift g (G.map χb) := hG.map_isHomLift g χb
  have hPiso : p𝒮.IsHomLift (𝟙 P.base) P.iso.hom := P.vertical
  have hP'iso : p𝒮.IsHomLift (𝟙 P'.base) P'.iso.hom := P'.vertical
  have hlhs : p𝒮.IsHomLift g (F.map χa ≫ P.iso.hom) := by
    simpa using IsHomLift.comp p𝒮 g (𝟙 P.base) (F.map χa) P.iso.hom
  have hrhs : p𝒮.IsHomLift g (P'.iso.hom ≫ G.map χb) :=
    IsHomLift.comp_lift_id_left' p𝒮 P'.base P'.iso.hom g (G.map χb)
  apply Functor.IsStronglyCartesian.ext p𝒮 f (G.map Φ.b) g
  rw [Category.assoc, Category.assoc, ← Φ.w, ← Category.assoc, ← Functor.map_comp, hχa_fac,
    ← Functor.map_comp, hχb_fac]
  exact Φ'.w

/-- A morphism into the domain of a morphism `Φ : P ⟶ Q` with strongly cartesian components
is determined by the morphism `g` of the base it lies over together with its composite with
`Φ`: each of its two components is, by the universal property of the corresponding component
of `Φ`. -/
lemma hom_ext_of_isStronglyCartesian_components
    {P Q P' : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G} (f : P.base ⟶ Q.base) (Φ : P ⟶ Q)
    (ha : p𝒳.IsStronglyCartesian f Φ.a) (hb : p𝒴.IsStronglyCartesian f Φ.b)
    (g : P'.base ⟶ P.base) (χ χ' : P' ⟶ P) (hχ : χ.hbase = g) (hχ' : χ'.hbase = g)
    (h : χ ≫ Φ = χ' ≫ Φ) : χ = χ' := by
  have h₁ : p𝒳.IsHomLift g χ.a := hχ ▸ χ.ha
  have h₂ : p𝒳.IsHomLift g χ'.a := hχ' ▸ χ'.ha
  have h₃ : p𝒴.IsHomLift g χ.b := hχ ▸ χ.hb
  have h₄ : p𝒴.IsHomLift g χ'.b := hχ' ▸ χ'.hb
  exact Hom.ext' (Functor.IsStronglyCartesian.ext p𝒳 f Φ.a g (by rw [← comp_a, ← comp_a, h]))
    (Functor.IsStronglyCartesian.ext p𝒴 f Φ.b g (by rw [← comp_b, ← comp_b, h]))

/-- **The analytic core.** Assume `F` and `G` are 1-morphisms of fibred categories. If a
morphism `Φ : P ⟶ Q` of the 2-fibre product lies over `f : R ⟶ T` for the structure
functor and both its components `Φ.a` and `Φ.b` are strongly cartesian over `f`, then `Φ`
itself is strongly cartesian over `f` for the structure functor. -/
lemma isStronglyCartesian_of_components
    (hF : Functor.IsFibredOneMorphism p𝒳 p𝒮 F) (hG : Functor.IsFibredOneMorphism p𝒴 p𝒮 G)
    {R T : 𝒞} {P Q : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G} (f : R ⟶ T) (Φ : P ⟶ Q)
    (hΦ : (structureFunctor p𝒳 p𝒴 p𝒮 F G).IsHomLift f Φ)
    (ha : p𝒳.IsStronglyCartesian f Φ.a) (hb : p𝒴.IsStronglyCartesian f Φ.b) :
    (structureFunctor p𝒳 p𝒴 p𝒮 F G).IsStronglyCartesian f Φ := by
  -- The base objects of `P`, `Q` coincide with `R`, `T`.
  obtain rfl : R = P.base := (IsHomLift.domain_eq (structureFunctor p𝒳 p𝒴 p𝒮 F G) f Φ).symm
  obtain rfl : T = Q.base := (IsHomLift.codomain_eq (structureFunctor p𝒳 p𝒴 p𝒮 F G) f Φ).symm
  refine ⟨?_⟩
  intro P' g Φ' hΦ'
  -- `Φ'.hbase` *is* the image of `Φ'` under the structure functor, so the equality is
  -- `IsHomLift.eq_of_isHomLift`; the instance is supplied by hand because the two spellings
  -- `(structureFunctor _ _ _ _ _).obj Q` and `Q.base` no longer unify at instance transparency.
  have hbase_eq : Φ'.hbase = g ≫ f :=
    (@IsHomLift.eq_of_isHomLift _ _ _ _ (structureFunctor p𝒳 p𝒴 p𝒮 F G) P' Q (g ≫ f) Φ'
      hΦ').symm
  have haΦ' : p𝒳.IsHomLift (g ≫ f) Φ'.a := hbase_eq ▸ Φ'.ha
  have hbΦ' : p𝒴.IsHomLift (g ≫ f) Φ'.b := hbase_eq ▸ Φ'.hb
  -- The induced lifts of the two components through the strongly cartesian `Φ.a`, `Φ.b`.
  set χa : P'.x ⟶ P.x := Functor.IsStronglyCartesian.map p𝒳 f Φ.a (g := g) rfl Φ'.a
  set χb : P'.y ⟶ P.y := Functor.IsStronglyCartesian.map p𝒴 f Φ.b (g := g) rfl Φ'.b
  have hχa_fac : χa ≫ Φ.a = Φ'.a := Functor.IsStronglyCartesian.fac p𝒳 f Φ.a (g := g) rfl Φ'.a
  have hχb_fac : χb ≫ Φ.b = Φ'.b := Functor.IsStronglyCartesian.fac p𝒴 f Φ.b (g := g) rfl Φ'.b
  have hχa_lift : p𝒳.IsHomLift g χa :=
    Functor.IsStronglyCartesian.map_isHomLift p𝒳 f Φ.a (g := g) rfl Φ'.a
  have hχb_lift : p𝒴.IsHomLift g χb :=
    Functor.IsStronglyCartesian.map_isHomLift p𝒴 f Φ.b (g := g) rfl Φ'.b
  set χ : P' ⟶ P := ⟨g, χa, χb, hχa_lift, hχb_lift,
    w_of_isStronglyCartesian hF hG f Φ hb hχa_lift hχb_lift Φ' hχa_fac hχb_fac⟩ with hχ_def
  have hχ_fac : χ ≫ Φ = Φ' := Hom.ext' hχa_fac hχb_fac
  refine ⟨χ, ⟨IsHomLift.map (structureFunctor p𝒳 p𝒴 p𝒮 F G) χ, hχ_fac⟩, ?_⟩
  rintro χ' ⟨hχ'_lift, hχ'_fac⟩
  exact hom_ext_of_isStronglyCartesian_components f Φ ha hb g χ' χ
    (@IsHomLift.eq_of_isHomLift _ _ _ _ (structureFunctor p𝒳 p𝒴 p𝒮 F G) P' P g χ' hχ'_lift).symm
    (by rw [hχ_def]) (hχ'_fac.trans hχ_fac.symm)

/-- **The canonical strongly cartesian lift.** For any object `Q` of the 2-fibre product
and any `f : V ⟶ Q.base` there is an object `P` and a morphism `Φ : P ⟶ Q` lying over `f`
which is strongly cartesian for the structure functor and whose two components are
strongly cartesian for `p𝒳` and `p𝒴`.

The components are the canonical lifts supplied by fibredness of `p𝒳` and `p𝒴`; the
vertical comparison isomorphism of `P` is produced by the universal property of the
strongly cartesian morphism `G.map b`. -/
lemma exists_isStronglyCartesian
    [p𝒳.IsFibered] [p𝒴.IsFibered]
    (hF : Functor.IsFibredOneMorphism p𝒳 p𝒮 F) (hG : Functor.IsFibredOneMorphism p𝒴 p𝒮 G)
    {V : 𝒞} (Q : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G) (f : V ⟶ Q.base) :
    ∃ (P : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G) (Φ : P ⟶ Q),
      (structureFunctor p𝒳 p𝒴 p𝒮 F G).IsStronglyCartesian f Φ ∧
        p𝒳.IsStronglyCartesian f Φ.a ∧ p𝒴.IsStronglyCartesian f Φ.b := by
  -- The canonical strongly cartesian lifts of `f` for `p𝒳` (ending at `Q.x`) and for
  -- `p𝒴` (ending at `Q.y`).
  set fx : 𝒳 := Functor.IsPreFibered.pullbackObj Q.hx f
  set a : fx ⟶ Q.x := Functor.IsPreFibered.pullbackMap Q.hx f
  set fy : 𝒴 := Functor.IsPreFibered.pullbackObj Q.hy f
  set b : fy ⟶ Q.y := Functor.IsPreFibered.pullbackMap Q.hy f
  have hSCa : p𝒳.IsStronglyCartesian f a := inferInstance
  have hSCb : p𝒴.IsStronglyCartesian f b := inferInstance
  have hSCFa : p𝒮.IsStronglyCartesian f (F.map a) := hF.map_isStronglyCartesian f a hSCa
  have hSCGb : p𝒮.IsStronglyCartesian f (G.map b) := hG.map_isStronglyCartesian f b hSCb
  -- `Q.iso.hom` is a vertical isomorphism, hence strongly cartesian over `𝟙 Q.base`, so
  -- `F.map a ≫ Q.iso.hom` is strongly cartesian over `f`.
  have hQisoHomLift : p𝒮.IsHomLift (𝟙 Q.base) Q.iso.hom := Q.vertical
  have hSCQiso : p𝒮.IsStronglyCartesian (𝟙 Q.base) Q.iso.hom :=
    Functor.IsStronglyCartesian.of_iso p𝒮 (𝟙 Q.base) Q.iso
  have hSCcomp : p𝒮.IsStronglyCartesian f (F.map a ≫ Q.iso.hom) := by
    simpa using Functor.IsStronglyCartesian.comp p𝒮 (f := f) (g := 𝟙 Q.base)
      (φ := F.map a) (ψ := Q.iso.hom)
  -- The vertical comparison isomorphism `F fx ≅ G fy` over `V`, from the universal property
  -- of the strongly cartesian `G.map b`.
  have hbase : f = (Iso.refl V).hom ≫ f := by simp
  set fφ : F.obj fx ≅ G.obj fy :=
    Functor.IsStronglyCartesian.domainIsoOfBaseIso p𝒮 hbase (G.map b) (F.map a ≫ Q.iso.hom)
  have hfφhom : fφ.hom =
      Functor.IsStronglyCartesian.map p𝒮 f (G.map b) hbase (F.map a ≫ Q.iso.hom) :=
    Functor.IsStronglyCartesian.domainIsoOfBaseIso_hom p𝒮 hbase (G.map b) (F.map a ≫ Q.iso.hom)
  have hfφvert : p𝒮.IsHomLift (𝟙 V) fφ.hom := by
    rw [hfφhom]
    simpa using
      Functor.IsStronglyCartesian.map_isHomLift p𝒮 f (G.map b) hbase (F.map a ≫ Q.iso.hom)
  have hsquare : F.map a ≫ Q.iso.hom = fφ.hom ≫ G.map b := by
    rw [hfφhom]
    exact (Functor.IsStronglyCartesian.fac p𝒮 f (G.map b) hbase (F.map a ≫ Q.iso.hom)).symm
  set P : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G :=
    { base := V, x := fx, y := fy, iso := fφ, vertical := hfφvert
      hx := Functor.IsPreFibered.pullbackObj_proj Q.hx f
      hy := Functor.IsPreFibered.pullbackObj_proj Q.hy f }
  set Φ : P ⟶ Q :=
    { hbase := f, a := a, b := b, w := hsquare
      ha := inferInstance, hb := inferInstance } with hΦ_def
  refine ⟨P, Φ, isStronglyCartesian_of_components hF hG f Φ ?_ hSCa hSCb, hSCa, hSCb⟩
  refine IsHomLift.of_fac' (structureFunctor p𝒳 p𝒴 p𝒮 F G) f Φ (a := P) (b := Q) rfl rfl ?_
  -- `change` re-elaborates the two `eqToHom`s at the reflexivity `V = V`, which is what lets
  -- `simp` discharge them; at the ambient reducibility they do not match `eqToHom_refl`.
  change Φ.hbase = eqToHom rfl ≫ f ≫ eqToHom rfl
  simp [hΦ_def]

/-- **The converse of the analytic core.** If `Φ : P ⟶ Q` is strongly cartesian for the
structure functor over `f`, then both of its components are strongly cartesian: `Φ.a` for
`p𝒳` and `Φ.b` for `p𝒴`.

Both follow at once by comparing `Φ` with the canonical lift `Φ₀` of `f` supplied by
`exists_isStronglyCartesian`, whose components are strongly cartesian by construction: two
strongly cartesian morphisms over the same `f` with the same target differ by an isomorphism
lying over an identity, which the projections preserve. That comparison is
`Functor.isStronglyCartesian_map_of_isStronglyCartesian_map`, applied to the first
projection and to the second. -/
lemma map_isStronglyCartesian_of_isStronglyCartesian
    [p𝒳.IsFibered] [p𝒴.IsFibered]
    (hF : Functor.IsFibredOneMorphism p𝒳 p𝒮 F) (hG : Functor.IsFibredOneMorphism p𝒴 p𝒮 G)
    {R T : 𝒞} {P Q : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G} (f : R ⟶ T) (Φ : P ⟶ Q)
    (hΦ : (structureFunctor p𝒳 p𝒴 p𝒮 F G).IsStronglyCartesian f Φ) :
    p𝒳.IsStronglyCartesian f Φ.a ∧ p𝒴.IsStronglyCartesian f Φ.b := by
  have := hΦ.toIsHomLift
  obtain rfl : T = Q.base := (IsHomLift.codomain_eq (structureFunctor p𝒳 p𝒴 p𝒮 F G) f Φ).symm
  obtain ⟨P₀, Φ₀, hΦ₀, hΦ₀a, hΦ₀b⟩ := exists_isStronglyCartesian hF hG Q f
  exact ⟨Functor.isStronglyCartesian_map_of_isStronglyCartesian_map (fst p𝒳 p𝒴 p𝒮 F G) p𝒳
      fst_comp_eq f Φ Φ₀ hΦ hΦ₀ hΦ₀a,
    Functor.isStronglyCartesian_map_of_isStronglyCartesian_map (snd p𝒳 p𝒴 p𝒮 F G) p𝒴
      snd_comp_eq f Φ Φ₀ hΦ hΦ₀ hΦ₀b⟩

end TwoFibreProductOver

/-- **Stacks 02XQ, fibredness.** If `p𝒳`, `p𝒴`, `p𝒮` are fibred categories over `𝒞` and
`F`, `G` are 1-morphisms of fibred categories over `𝒞`, then the structure functor of the
2-fibre product `𝒳 ×_𝒮 𝒴` exhibits it as a fibred category over `𝒞`. -/
@[stacks 02XQ]
theorem TwoFibreProductOver.isFibered_structureFunctor
    (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (p𝒮 : 𝒮 ⥤ 𝒞) (F : 𝒳 ⥤ 𝒮) (G : 𝒴 ⥤ 𝒮)
    [p𝒳.IsFibered] [p𝒴.IsFibered] [p𝒮.IsFibered]
    (hF : Functor.IsFibredOneMorphism p𝒳 p𝒮 F)
    (hG : Functor.IsFibredOneMorphism p𝒴 p𝒮 G) :
    (TwoFibreProductOver.structureFunctor p𝒳 p𝒴 p𝒮 F G).IsFibered := by
  refine Functor.IsFibered.of_exists_isStronglyCartesian fun Q _ f => ?_
  obtain ⟨P, Φ, hΦ, -, -⟩ := TwoFibreProductOver.exists_isStronglyCartesian hF hG Q f
  exact ⟨P, Φ, hΦ⟩

/-- **Stacks 02XQ, first projection.** Under the hypotheses of
`TwoFibreProductOver.isFibered_structureFunctor`, the first projection `π₁` is a 1-morphism
of fibred categories over `𝒞`: it is strictly over `𝒞` and preserves strongly cartesian
morphisms. -/
@[stacks 02XQ]
theorem TwoFibreProductOver.fst_isFibredOneMorphism
    (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (p𝒮 : 𝒮 ⥤ 𝒞) (F : 𝒳 ⥤ 𝒮) (G : 𝒴 ⥤ 𝒮)
    [p𝒳.IsFibered] [p𝒴.IsFibered] [p𝒮.IsFibered]
    (hF : Functor.IsFibredOneMorphism p𝒳 p𝒮 F)
    (hG : Functor.IsFibredOneMorphism p𝒴 p𝒮 G) :
    Functor.IsFibredOneMorphism (TwoFibreProductOver.structureFunctor p𝒳 p𝒴 p𝒮 F G) p𝒳
      (TwoFibreProductOver.fst p𝒳 p𝒴 p𝒮 F G) where
  comp_eq := TwoFibreProductOver.fst_comp_eq
  map_isStronglyCartesian := by
    intro _ _ f _ _ Φ hΦ
    exact (TwoFibreProductOver.map_isStronglyCartesian_of_isStronglyCartesian hF hG f Φ hΦ).1

/-- **Stacks 02XQ, second projection.** Under the hypotheses of
`TwoFibreProductOver.isFibered_structureFunctor`, the second projection `π₂` is a 1-morphism
of fibred categories over `𝒞`. -/
@[stacks 02XQ]
theorem TwoFibreProductOver.snd_isFibredOneMorphism
    (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (p𝒮 : 𝒮 ⥤ 𝒞) (F : 𝒳 ⥤ 𝒮) (G : 𝒴 ⥤ 𝒮)
    [p𝒳.IsFibered] [p𝒴.IsFibered] [p𝒮.IsFibered]
    (hF : Functor.IsFibredOneMorphism p𝒳 p𝒮 F)
    (hG : Functor.IsFibredOneMorphism p𝒴 p𝒮 G) :
    Functor.IsFibredOneMorphism (TwoFibreProductOver.structureFunctor p𝒳 p𝒴 p𝒮 F G) p𝒴
      (TwoFibreProductOver.snd p𝒳 p𝒴 p𝒮 F G) where
  comp_eq := TwoFibreProductOver.snd_comp_eq
  map_isStronglyCartesian := by
    intro _ _ f _ _ Φ hΦ
    exact (TwoFibreProductOver.map_isStronglyCartesian_of_isStronglyCartesian hF hG f Φ hΦ).2

end CategoryTheory
