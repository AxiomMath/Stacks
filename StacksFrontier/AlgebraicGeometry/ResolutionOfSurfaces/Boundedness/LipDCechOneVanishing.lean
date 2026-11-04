module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.LipDPuncturedRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.CechToCohomology.DegreeOneFlasqueVanishing
public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.ModuleRestrictionVanishing

/-!
# Čech cocycles of the unit module are coboundaries when `H¹` vanishes

Let `R` be a sheaf of rings on a topological space `T` with `H¹(T, R) = 0`, and let `(Vⱼ)` be an
open cover of `T`.  Every Čech `1`-cocycle `q` of the unit module `R` for the cover is a
coboundary: there are sections `uⱼ ∈ Γ(Vⱼ, R)` with `q_{ab} = u_a|_{V_a ∩ V_b} - u_b|_{V_a ∩ V_b}`.

## The argument

Take an injective resolution `R → I⁰ → I¹ → ⋯`.  The underlying abelian sheaf of the injective
module `I⁰` is flasque, so its first Čech cohomology for the cover vanishes
(`Stacks.Cohomology.CechOne.exists_cechD_eq_of_isFlasque`): the image of `q` in `I⁰` is
`w_a - w_b` for sections `w_a ∈ Γ(V_a, I⁰)`.  The sections `d w_a ∈ Γ(V_a, I¹)` agree on overlaps,
since `d` kills the image of `R`, so they glue to a cocycle `c ∈ Γ(T, I¹)`.  Its class in
`H¹(T, R)` vanishes, so `c = d y` for some `y ∈ Γ(T, I⁰)`.  Then `w_a - y|_{V_a}` is killed by
`d`, hence is the image of a section `u_a` of `R`, and these are the required primitives.

## Main results

* `AlgebraicGeometry.PuncturedRestriction.exists_eq_sub_of_cocycle`: the vanishing.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.PuncturedRestriction

section CechOne

variable {T : Type u} [TopologicalSpace T] (R : Sheaf (Opens.grothendieckTopology T) RingCat.{u})

/-- The underlying abelian sheaf of a sheaf of modules, as a sheaf on `TopCat.of T`. -/
def topSheaf (M : SheafOfModules.{u} R) : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of T) :=
  ⟨((SheafOfModules.toSheaf R).obj M).obj, ((SheafOfModules.toSheaf R).obj M).property⟩

/-- The restriction of the Čech machinery is restriction of sections. -/
theorem restr_topSheaf (M : SheafOfModules.{u} R) {U V : Opens T} (h : U ≤ V)
    (s : (secF R V).obj M) :
    CechCochains.restr (X := TopCat.of T) (topSheaf R M).presheaf h s =
      (secRestrict R h).app M s :=
  rfl

/-- The Čech differential of a `0`-cochain, as a difference of restrictions of sections. -/
theorem cechD_zero_topSheaf {J : Type u} (V : J → Opens T) (M : SheafOfModules.{u} R)
    (b : CechCochains.Cochain (X := TopCat.of T) V (topSheaf R M).presheaf 0) (i : Fin 2 → J) :
    (CechCochains.cechD (X := TopCat.of T) V (topSheaf R M).presheaf 0 b i :
        (secF R (CechCochains.inter (X := TopCat.of T) V i)).obj M) =
      (secRestrict R (CechCochains.inter_le_omit (X := TopCat.of T) V i 0)).app M
          (b (i ∘ Fin.succAbove 0)) -
        (secRestrict R (CechCochains.inter_le_omit (X := TopCat.of T) V i 1)).app M
          (b (i ∘ Fin.succAbove 1)) := by
  have hs2 : ∀ {N : Type u} [AddCommGroup N] (x y : N),
      (-1 : ℤ) ^ ((0 : Fin 2) : ℕ) • x + (-1 : ℤ) ^ ((1 : Fin 2) : ℕ) • y = x - y := by
    intro N _ x y
    simp [sub_eq_add_neg]
  exact (CechCochains.cechD_apply (X := TopCat.of T) V b i).trans
    ((Fin.sum_univ_two _).trans (hs2 _ _))

/-- Restriction along `U ≤ U` is the identity. -/
theorem secRestrict_app_self (M : SheafOfModules.{u} R) {U : Opens T} (h : U ≤ U)
    (s : (secF R U).obj M) : (secRestrict R h).app M s = s := by
  change ((SheafOfModules.toSheaf R).obj M).obj.map (homOfLE h).op s = s
  rw [show (homOfLE h).op = 𝟙 (op U) from rfl, CategoryTheory.Functor.map_id]
  rfl

/-- Two restrictions with the same source and target agree. -/
theorem secRestrict_app_congr (M : SheafOfModules.{u} R) {U V : Opens T} (h h' : U ≤ V)
    (s : (secF R V).obj M) : (secRestrict R h).app M s = (secRestrict R h').app M s := rfl

/-- Two restrictions of a Čech cochain of `topSheaf R M` along equal indices agree. -/
theorem secRestrict_app_cochain_congr (M : SheafOfModules.{u} R) {J : Type u} {V : J → Opens T}
    {p : ℕ} (s : CechCochains.Cochain (X := TopCat.of T) V (topSheaf R M).presheaf p)
    {i i' : Fin (p + 1) → J} (h : i = i') {W : Opens T}
    (h₁ : W ≤ CechCochains.inter (X := TopCat.of T) V i)
    (h₂ : W ≤ CechCochains.inter (X := TopCat.of T) V i') :
    (secRestrict R h₁).app M (s i) = (secRestrict R h₂).app M (s i') := by
  subst h
  rfl

variable [HasSheafify (Opens.grothendieckTopology T) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology T).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [EnoughInjectives (SheafOfModules.{u} R)]

/-- The image in `I⁰` of a family of sections of the unit module on the pairwise overlaps, as a
Čech `1`-cochain. -/
def ι₀Cochain (I : InjectiveResolution (SheafOfModules.unit R)) {J : Type u} (V : J → Opens T)
    (q : ∀ a b, (secF R (V a ⊓ V b)).obj (SheafOfModules.unit R)) :
    CechCochains.Cochain (X := TopCat.of T) V (topSheaf R (I.cocomplex.X 0)).presheaf 1 :=
  fun i => (secRestrict R (le_inf (iInf_le _ 0) (iInf_le _ 1) :
    CechCochains.inter (X := TopCat.of T) V i ≤ V (i 0) ⊓ V (i 1))).app _
      ((secF R _).map (ι₀ I) (q (i 0) (i 1)))

omit [HasSheafify (Opens.grothendieckTopology T) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology T).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [EnoughInjectives (SheafOfModules.{u} R)] in
/-- Restricting `ι₀Cochain` is restricting the original family, then mapping it to `I⁰`. -/
theorem secRestrict_app_ι₀Cochain (I : InjectiveResolution (SheafOfModules.unit R))
    {J : Type u} (V : J → Opens T) (q : ∀ a b, (secF R (V a ⊓ V b)).obj (SheafOfModules.unit R))
    (i : Fin 2 → J) {W : Opens T} (h : W ≤ CechCochains.inter (X := TopCat.of T) V i)
    {a b : J} (ha : i 0 = a) (hb : i 1 = b) (hab : W ≤ V a ⊓ V b) :
    (secRestrict R h).app _ (ι₀Cochain R I V q i) =
      (secF R W).map (ι₀ I) ((secRestrict R hab).app _ (q a b)) := by
  subst ha hb
  simp only [ι₀Cochain]
  rw [secRestrict_app_comp, secRestrict_app_map]

omit [HasSheafify (Opens.grothendieckTopology T) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology T).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [EnoughInjectives (SheafOfModules.{u} R)] in
/-- The image in `I⁰` of a cocycle of the unit module is a Čech cocycle. -/
theorem cechD_ι₀Cochain (I : InjectiveResolution (SheafOfModules.unit R))
    {J : Type u} (V : J → Opens T)
    (q : ∀ a b, (secF R (V a ⊓ V b)).obj (SheafOfModules.unit R))
    (hq : ∀ a b c,
      (secRestrict R (le_inf (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) :
          V a ⊓ V b ⊓ V c ≤ V a ⊓ V b)).app _ (q a b) +
        (secRestrict R (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          V a ⊓ V b ⊓ V c ≤ V b ⊓ V c)).app _ (q b c) =
      (secRestrict R (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
          V a ⊓ V b ⊓ V c ≤ V a ⊓ V c)).app _ (q a c)) :
    CechCochains.cechD (X := TopCat.of T) V (topSheaf R (I.cocomplex.X 0)).presheaf 1
      (ι₀Cochain R I V q) = 0 := by
  have hterm : ∀ (i : Fin 2 → J) {W : Opens T}
      (h : W ≤ CechCochains.inter (X := TopCat.of T) V i)
      {a b : J} (ha : i 0 = a) (hb : i 1 = b) (hab : W ≤ V a ⊓ V b),
      CechCochains.restr (X := TopCat.of T) (topSheaf R (I.cocomplex.X 0)).presheaf h
          (ι₀Cochain R I V q i) =
        (secF R W).map (ι₀ I) ((secRestrict R hab).app _ (q a b)) :=
    fun i W h a b ha hb hab =>
      (restr_topSheaf R _ h _).trans (secRestrict_app_ι₀Cochain R I V q i h ha hb hab)
  funext x
  rw [CechCochains.cechD_apply, Fin.sum_univ_three, CechCochains.Cochain.zero_apply]
  have hx : CechCochains.inter (X := TopCat.of T) V x ≤ V (x 0) ⊓ V (x 1) ⊓ V (x 2) :=
    le_inf (le_inf (iInf_le _ 0) (iInf_le _ 1)) (iInf_le _ 2)
  rw [hterm _ _ (a := x 1) (b := x 2) rfl rfl (le_inf (hx.trans (inf_le_left.trans inf_le_right))
      (hx.trans inf_le_right)),
    hterm _ _ (a := x 0) (b := x 2) rfl rfl (le_inf (hx.trans (inf_le_left.trans inf_le_left))
      (hx.trans inf_le_right)),
    hterm _ _ (a := x 0) (b := x 1) rfl rfl (le_inf (hx.trans (inf_le_left.trans inf_le_left))
      (hx.trans (inf_le_left.trans inf_le_right)))]
  have h3 := congrArg ((secF R _).map (ι₀ I))
    (congrArg ((secRestrict R hx).app _) (hq (x 0) (x 1) (x 2)))
  rw [map_add, map_add, secRestrict_app_comp, secRestrict_app_comp, secRestrict_app_comp,
    ← sub_eq_zero] at h3
  refine Eq.trans ?_ h3
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, neg_one_sq]
  abel

omit [HasSheafify (Opens.grothendieckTopology T) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology T).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [EnoughInjectives (SheafOfModules.{u} R)] in
/-- **Step 1: the image of the cocycle in `I⁰` is a Čech coboundary**, because the underlying
abelian sheaf of the injective module `I⁰` is flasque. -/
theorem exists_sub_eq_ι₀_of_cocycle (I : InjectiveResolution (SheafOfModules.unit R))
    {J : Type u} (V : J → Opens T)
    (q : ∀ a b, (secF R (V a ⊓ V b)).obj (SheafOfModules.unit R))
    (hq : ∀ a b c,
      (secRestrict R (le_inf (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) :
          V a ⊓ V b ⊓ V c ≤ V a ⊓ V b)).app _ (q a b) +
        (secRestrict R (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          V a ⊓ V b ⊓ V c ≤ V b ⊓ V c)).app _ (q b c) =
      (secRestrict R (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
          V a ⊓ V b ⊓ V c ≤ V a ⊓ V c)).app _ (q a c)) :
    ∃ w : ∀ a, (secF R (V a)).obj (I.cocomplex.X 0), ∀ a c, (secF R _).map (ι₀ I) (q a c) =
      (secRestrict R inf_le_left).app _ (w a) - (secRestrict R inf_le_right).app _ (w c) := by
  have : (topSheaf R (I.cocomplex.X 0)).IsFlasque :=
    Stacks.Topology.isFlasque_toSheaf_of_injective (X := TopCat.of T) R (I.cocomplex.X 0)
  obtain ⟨b, hb⟩ := Stacks.Cohomology.CechOne.exists_cechD_eq_of_isFlasque (X := TopCat.of T) V
    (topSheaf R (I.cocomplex.X 0)) (ι₀Cochain R I V q) (cechD_ι₀Cochain R I V q hq)
  have hle1 : ∀ a : J, V a ≤ CechCochains.inter (X := TopCat.of T) V (fun _ : Fin 1 => a) :=
    fun a => le_iInf fun _ => le_rfl
  let w : ∀ a, (secF R (V a)).obj (I.cocomplex.X 0) := fun a =>
    -(secRestrict R (hle1 a)).app _ (b (fun _ => a))
  refine ⟨w, fun a c => ?_⟩
  let i : Fin 2 → J := ![a, c]
  have hi : V a ⊓ V c ≤ CechCochains.inter (X := TopCat.of T) V i :=
    le_iInf fun k => by fin_cases k <;> [exact inf_le_left; exact inf_le_right]
  have h1 := congrArg ((secRestrict R hi).app _) (congrFun hb i)
  rw [secRestrict_app_ι₀Cochain R I V q i hi (a := a) (b := c) rfl rfl le_rfl,
    secRestrict_app_self] at h1
  have e01 : ∀ (k : Fin 2) (x : J) (hk : i ∘ Fin.succAbove k = fun _ => x)
      (hx : V a ⊓ V c ≤ V x),
      (secRestrict R hi).app _ ((secRestrict R
        (CechCochains.inter_le_omit (X := TopCat.of T) V i k)).app _ (b (i ∘ Fin.succAbove k))) =
      (secRestrict R (hx.trans (hle1 x))).app _ (b (fun _ => x)) := fun k x hk hx =>
    (secRestrict_app_comp R hi _ _ _).trans (secRestrict_app_cochain_congr R _ b hk _ _)
  have e23 : ∀ (x : J) (hx : V a ⊓ V c ≤ V x),
      (secRestrict R hx).app _ (w x) =
        -(secRestrict R (hx.trans (hle1 x))).app _ (b (fun _ => x)) := fun x hx => by
    simp only [w, map_neg]
    exact congrArg Neg.neg (secRestrict_app_comp R _ _ _ _)
  rw [← h1, cechD_zero_topSheaf, map_sub,
    e01 0 c (by funext k; fin_cases k; rfl) inf_le_right,
    e01 1 a (by funext k; fin_cases k; rfl) inf_le_left, e23 a inf_le_left, e23 c inf_le_right]
  abel

omit [HasSheafify (Opens.grothendieckTopology T) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology T).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [EnoughInjectives (SheafOfModules.{u} R)] in
/-- **Step 2: the differentials of the primitives in `I⁰` glue to a global cocycle of `I¹`.** -/
theorem exists_glue_d_of_sub_eq_ι₀ (I : InjectiveResolution (SheafOfModules.unit R))
    {J : Type u} (V : J → Opens T) (hV : ∀ x, ∃ j, x ∈ V j)
    (q : ∀ a b, (secF R (V a ⊓ V b)).obj (SheafOfModules.unit R))
    (w : ∀ a, (secF R (V a)).obj (I.cocomplex.X 0))
    (hw : ∀ a c, (secF R _).map (ι₀ I) (q a c) =
      (secRestrict R inf_le_left).app _ (w a) - (secRestrict R inf_le_right).app _ (w c)) :
    ∃ c : (secF R ⊤).obj (I.cocomplex.X 1),
      (∀ a, (secRestrict R (le_top : V a ≤ ⊤)).app _ c =
        (secF R (V a)).map (I.cocomplex.d 0 1) (w a)) ∧
      (secF R ⊤).map (I.cocomplex.d 1 2) c = 0 := by
  let e : ∀ a, (secF R (V a)).obj (I.cocomplex.X 1) := fun a =>
    (secF R (V a)).map (I.cocomplex.d 0 1) (w a)
  have hcompat : ∀ a c, (secRestrict R inf_le_left).app _ (e a) =
      (secRestrict R (inf_le_right : V a ⊓ V c ≤ V c)).app _ (e c) := by
    intro a c
    have h := congrArg ((secF R _).map (I.cocomplex.d 0 1)) (hw a c)
    rw [secF_map_ι₀_d_apply I, map_sub, ← secRestrict_app_map, ← secRestrict_app_map] at h
    exact sub_eq_zero.mp h.symm
  have hcov : (⊤ : Opens T) ≤ iSup V := fun x _ => Opens.mem_iSup.mpr (hV x)
  obtain ⟨c, hc'⟩ : ∃ c : (secF R ⊤).obj (I.cocomplex.X 1),
      ∀ a, (secRestrict R (le_top : V a ≤ ⊤)).app _ c = e a :=
    (TopCat.Sheaf.existsUnique_gluing' (topSheaf R (I.cocomplex.X 1)) V ⊤
      (fun a => homOfLE le_top) hcov e hcompat).exists
  refine ⟨c, hc', TopCat.Sheaf.eq_of_locally_eq' (topSheaf R (I.cocomplex.X 2)) V ⊤
    (fun a => homOfLE le_top) hcov _ _ (fun a => ?_)⟩
  change (secRestrict R le_top).app _ ((secF R ⊤).map (I.cocomplex.d 1 2) c) =
    (secRestrict R le_top).app _ 0
  rw [secRestrict_app_map, hc', map_zero]
  change (secF R (V a)).map (I.cocomplex.d 1 2) ((secF R (V a)).map (I.cocomplex.d 0 1) (w a))
    = 0
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, I.cocomplex.d_comp_d,
    Functor.map_zero]
  rfl

/-- **A Čech `1`-cocycle of the unit module is a coboundary when `H¹(T, R)` vanishes.** -/
theorem exists_eq_sub_of_cocycle
    (hH : IsZero (Hgroup R ⊤ 1 (SheafOfModules.unit R))) {J : Type u} (V : J → Opens T)
    (hV : ∀ x, ∃ j, x ∈ V j) (q : ∀ a b, (secF R (V a ⊓ V b)).obj (SheafOfModules.unit R))
    (hq : ∀ a b c,
      (secRestrict R (le_inf (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) :
          V a ⊓ V b ⊓ V c ≤ V a ⊓ V b)).app _ (q a b) +
        (secRestrict R (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          V a ⊓ V b ⊓ V c ≤ V b ⊓ V c)).app _ (q b c) =
      (secRestrict R (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
          V a ⊓ V b ⊓ V c ≤ V a ⊓ V c)).app _ (q a c)) :
    ∃ u : ∀ a, (secF R (V a)).obj (SheafOfModules.unit R),
      ∀ a b, q a b = (secRestrict R inf_le_left).app _ (u a) -
        (secRestrict R inf_le_right).app _ (u b) := by
  let I : InjectiveResolution (SheafOfModules.unit R) := InjectiveResolution.of _
  have hexact := exact_mono_secF_ι₀ I
  have hinj : ∀ W : Opens T, Function.Injective ((secF R W).map (ι₀ I)) := fun W =>
    (AddCommGrpCat.mono_iff_injective _).mp (hexact W).2
  obtain ⟨w, hw⟩ := exists_sub_eq_ι₀_of_cocycle R I V q hq
  obtain ⟨c, hc', hdc⟩ := exists_glue_d_of_sub_eq_ι₀ R I V hV q w hw
  obtain ⟨zc, hzc⟩ : ∃ zc : (secCx R I ⊤).cycles 1, (secCx R I ⊤).iCycles 1 zc = c := by
    let K := secCx R I ⊤
    let Sk := ShortComplex.mk (K.iCycles 1) (K.d 1 2) (K.iCycles_d 1 2)
    exact (ShortComplex.ab_exact_iff Sk).mp
      (ShortComplex.exact_of_f_is_kernel Sk (K.cyclesIsKernel 1 2 (by simp))) c hdc
  have hπ : (secCx R I ⊤).homologyπ 1 zc = 0 := by
    have hZ : IsZero ((secCx R I ⊤).homology 1) :=
      hH.of_iso (I.isoRightDerivedObj (secF R ⊤) 1).symm
    simpa using congrArg (fun f => f ((secCx R I ⊤).homologyπ 1 zc)) (hZ.eq_of_src (𝟙 _) 0)
  obtain ⟨y, hy⟩ := (homologyπ_one_eq_zero_iff _ zc).mp hπ
  rw [hzc] at hy
  have hu : ∀ a, ∃ t : (secF R (V a)).obj (SheafOfModules.unit R),
      (secF R (V a)).map (ι₀ I) t = w a - (secRestrict R (le_top : V a ≤ ⊤)).app _ y := by
    intro a
    refine (ShortComplex.ab_exact_iff _).mp (hexact (V a)).1 _ ?_
    change (secF R (V a)).map (I.cocomplex.d 0 1) (_ - _) = 0
    rw [map_sub, ← secRestrict_app_map]
    change (secF R (V a)).map (I.cocomplex.d 0 1) (w a) -
      (secRestrict R le_top).app _ ((secF R ⊤).map (I.cocomplex.d 0 1) y) = 0
    rw [show (secF R ⊤).map (I.cocomplex.d 0 1) y = c from hy, hc', sub_self]
  choose u hu using hu
  refine ⟨u, fun a c => hinj _ ?_⟩
  rw [hw, map_sub, ← secRestrict_app_map, ← secRestrict_app_map, hu, hu, map_sub, map_sub,
    secRestrict_app_comp, secRestrict_app_comp]
  abel

end CechOne

end AlgebraicGeometry.PuncturedRestriction

end
